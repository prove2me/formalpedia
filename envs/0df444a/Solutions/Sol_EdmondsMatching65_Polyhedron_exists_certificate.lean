-- Prove2me | solution 1 for EdmondsMatching65.Polyhedron.exists_certificate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:14:50.08073+00:00
-- url     : https://prove2.me/submissions/d659ad89-42fe-4345-a00f-15d0200948bb

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_DualProgram
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron
import Theorems.Thm_EdmondsMatching65_Polyhedron_theorem_P_vertices_eq_matching_vectors

open scoped Matrix

namespace EdmondsMatching65.Polyhedron

namespace ECF

open Matrix

set_option linter.unusedSectionVars false

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

def PFeas (M : Matrix κ ι ℝ) (r : κ → ℝ) (z : ι → ℝ) : Prop := (∀ j, 0 ≤ z j) ∧ M *ᵥ z = r

noncomputable def supp (z : ι → ℝ) : Finset ι := Finset.univ.filter (fun j => z j ≠ 0)

def ColLI (M : Matrix κ ι ℝ) (S : Finset ι) : Prop :=
  LinearIndependent ℝ (fun j : S => Mᵀ (j : ι))

lemma mem_supp {z : ι → ℝ} {j : ι} : j ∈ supp z ↔ z j ≠ 0 := by simp [supp]

lemma sum_sub_eq_mulVec (M : Matrix κ ι ℝ) (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ j, j ∉ S → w j = 0) :
    ∑ j : S, w j • Mᵀ (j : ι) = M *ᵥ w := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul, mulVec, dotProduct]
  rw [Finset.sum_coe_sort S (fun j => w j * M i j)]
  rw [Finset.sum_subset (Finset.subset_univ S)]
  · exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · intro j _ hj; simp [hw j hj]

lemma reduce (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (L : ℝ)
    (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z) :
    ∀ n, ∀ z, (supp z).card = n → PFeas M r z →
      ∃ z', PFeas M r z' ∧ c ⬝ᵥ z' ≤ c ⬝ᵥ z ∧ supp z' ⊆ supp z ∧ ColLI M (supp z') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hn hz
  by_cases hli : ColLI M (supp z)
  · exact ⟨z, hz, le_rfl, subset_rfl, hli⟩
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
  let d : ι → ℝ := fun j => if h : j ∈ supp z then g ⟨j, h⟩ else 0
  have hdS : ∀ j, j ∉ supp z → d j = 0 := by intro j hj; simp [d, hj]
  have hMd : M *ᵥ d = 0 := by
    rw [← sum_sub_eq_mulVec M (supp z) d hdS]
    convert hg using 2 with j
    simp [d]
  have hdi0 : d i0 ≠ 0 := by simpa [d] using hi0
  have hzpos : ∀ j, 0 ≤ z j := hz.1
  -- unboundedness contradiction
  have unb : ∀ e : ι → ℝ, M *ᵥ e = 0 → (∀ j, 0 ≤ e j) → c ⬝ᵥ e < 0 → False := by
    intro e hMe he hce
    set s := (c ⬝ᵥ z - L + 1) / (-(c ⬝ᵥ e)) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith [hL z hz]) (by linarith)
    have hf : PFeas M r (z + s • e) := ⟨fun j => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hzpos j) (mul_nonneg hs0 (he j)), by
      rw [mulVec_add, mulVec_smul, hMe, smul_zero, add_zero, hz.2]⟩
    have := hL _ hf
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have hse : s * (c ⬝ᵥ e) = -(c ⬝ᵥ z - L + 1) := by
      have hne : -(c ⬝ᵥ e) ≠ 0 := by linarith
      have h2 : (c ⬝ᵥ z - L + 1) / -(c ⬝ᵥ e) * -(c ⬝ᵥ e) = c ⬝ᵥ z - L + 1 := div_mul_cancel₀ _ hne
      rw [hs]; linear_combination -h2
    linarith
  obtain ⟨e, hMe, heS, hce, j0, hj0⟩ : ∃ e : ι → ℝ, M *ᵥ e = 0 ∧ (∀ j, j ∉ supp z → e j = 0) ∧
      c ⬝ᵥ e ≤ 0 ∧ ∃ j, e j < 0 := by
    obtain ⟨d1, hMd1, hd1S, hcd1, hd1i0⟩ : ∃ d1 : ι → ℝ, M *ᵥ d1 = 0 ∧
        (∀ j, j ∉ supp z → d1 j = 0) ∧ c ⬝ᵥ d1 ≤ 0 ∧ d1 i0 ≠ 0 := by
      by_cases h : c ⬝ᵥ d ≤ 0
      · exact ⟨d, hMd, hdS, h, hdi0⟩
      · refine ⟨-d, by rw [mulVec_neg, hMd, neg_zero], fun j hj => by simp [hdS j hj], ?_, ?_⟩
        · rw [dotProduct_neg]; linarith
        · simpa using hdi0
    by_cases hneg : ∃ j, d1 j < 0
    · exact ⟨d1, hMd1, hd1S, hcd1, hneg⟩
    push_neg at hneg
    rcases hcd1.lt_or_eq with hlt | heq
    · exact (unb d1 hMd1 hneg hlt).elim
    · refine ⟨-d1, by rw [mulVec_neg, hMd1, neg_zero], fun j hj => by simp [hd1S j hj],
        by rw [dotProduct_neg, heq, neg_zero], i0, ?_⟩
      have := lt_of_le_of_ne (hneg i0) (Ne.symm hd1i0)
      simp only [Pi.neg_apply]; linarith
  let P := Finset.univ.filter (fun j => e j < 0)
  obtain ⟨jm, hjmP, hjm⟩ := P.exists_min_image (fun j => z j / (-e j)) ⟨j0, by simp [P, hj0]⟩
  have hejm : e jm < 0 := by simpa [P] using hjmP
  set t := z jm / (-e jm) with ht
  have ht0 : 0 ≤ t := div_nonneg (hzpos jm) (by linarith)
  let z' := z + t • e
  have hz' : PFeas M r z' := by
    refine ⟨fun j => ?_, by simp only [z']; rw [mulVec_add, mulVec_smul, hMe, smul_zero, add_zero, hz.2]⟩
    simp only [z', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hej : e j < 0
    · have h1 : t ≤ z j / (-e j) := hjm j (by simp [P, hej])
      rw [le_div_iff₀ (by linarith)] at h1
      linarith
    · push_neg at hej
      exact add_nonneg (hzpos j) (mul_nonneg ht0 hej)
  have hsub : supp z' ⊆ supp z := by
    intro j hj
    rw [mem_supp] at hj ⊢
    intro hzj
    apply hj
    have : e j = 0 := by
      by_contra hne
      exact absurd (heS j) (by
        intro h'
        have : j ∉ supp z := by rw [mem_supp]; exact fun h => h hzj
        exact hne (h' this))
    simp [z', hzj, this]
  have hjm_in : jm ∈ supp z := by
    by_contra h; exact absurd (heS jm h) (ne_of_lt hejm)
  have hjm_out : jm ∉ supp z' := by
    rw [mem_supp, not_not]
    simp only [z', Pi.add_apply, Pi.smul_apply, smul_eq_mul, ht]
    have hne : e jm ≠ 0 := ne_of_lt hejm
    rw [div_neg, neg_mul, div_mul_cancel₀ _ hne]; ring
  have hlt : (supp z').card < n := by
    rw [← hn]
    exact Finset.card_lt_card ⟨hsub, fun h => hjm_out (h hjm_in)⟩
  obtain ⟨z'', h1, h2, h3, h4⟩ := ih _ hlt z' rfl hz'
  refine ⟨z'', h1, le_trans h2 ?_, h3.trans hsub, h4⟩
  simp only [z', dotProduct_add, dotProduct_smul, smul_eq_mul]
  nlinarith


def cone (M : Matrix κ ι ℝ) : Set (κ → ℝ) := (M.mulVecLin) '' {z | ∀ j, 0 ≤ z j}

lemma cone_closed (M : Matrix κ ι ℝ) : IsClosed (cone M) := by
  have heq : cone M = ⋃ (S : Finset ι) (_ : ColLI M S),
      (Fintype.linearCombination ℝ (fun j : S => Mᵀ (j : ι))) '' {w | ∀ j, 0 ≤ w j} := by
    ext t
    simp only [cone, Set.mem_image, Set.mem_setOf_eq, Set.mem_iUnion, mulVecLin_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨z', hz', _, _, hli⟩ := reduce M (M *ᵥ z) 0 0 (fun _ _ => by simp) _ z rfl ⟨hz, rfl⟩
      refine ⟨supp z', hli, fun j => z' j, fun j => hz'.1 j, ?_⟩
      rw [Fintype.linearCombination_apply, sum_sub_eq_mulVec M (supp z') z'
        (fun j hj => by rw [mem_supp, not_not] at hj; exact hj), hz'.2]
    · rintro ⟨S, _, w, hw, rfl⟩
      refine ⟨fun j => if h : j ∈ S then w ⟨j, h⟩ else 0, fun j => ?_, ?_⟩
      · by_cases h : j ∈ S <;> simp [h, hw]
      · rw [Fintype.linearCombination_apply, ← sum_sub_eq_mulVec M S _ (fun j hj => by simp [hj])]
        simp
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro S
  apply isClosed_iUnion_of_finite
  intro hli
  have hinj := linearIndependent_iff_injective_fintypeLinearCombination.mp hli
  have hker : LinearMap.ker (Fintype.linearCombination ℝ (fun j : S => Mᵀ (j : ι))) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  apply (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap
  have : {w : S → ℝ | ∀ j, 0 ≤ w j} = ⋂ j, {w | 0 ≤ w j} := by ext; simp
  rw [this]
  exact isClosed_iInter (fun j => isClosed_le continuous_const (continuous_apply j))

lemma farkas (M : Matrix κ ι ℝ) (t : κ → ℝ) (ht : t ∉ cone M) :
    ∃ y : κ → ℝ, (∀ j, 0 ≤ (y ᵥ* M) j) ∧ y ⬝ᵥ t < 0 := by
  have hconv : Convex ℝ (cone M) := by
    apply Convex.linear_image
    have : {z : ι → ℝ | ∀ j, 0 ≤ z j} = Set.Ici 0 := by ext; simp [Pi.le_def]
    rw [this]; exact convex_Ici 0
  obtain ⟨f, u, hfu, hut⟩ := geometric_hahn_banach_closed_point hconv (cone_closed M) ht
  have h0 : 0 < u := by
    have := hfu 0 ⟨0, fun _ => le_rfl, by simp⟩
    simpa using this
  have hneg : ∀ a ∈ cone M, f a ≤ 0 := by
    intro a ha
    by_contra h
    push_neg at h
    obtain ⟨z, hz, rfl⟩ := ha
    have hs : 0 ≤ u / f (M.mulVecLin z) + 1 := by positivity
    have hmem : (u / f (M.mulVecLin z) + 1) • M.mulVecLin z ∈ cone M :=
      ⟨(u / f (M.mulVecLin z) + 1) • z, fun j => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hs (hz j), by simp⟩
    have := hfu _ hmem
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ (ne_of_gt h)] at this
    linarith
  have hf : ∀ v : κ → ℝ, f v = ∑ i, v i * f (fun j => if i = j then 1 else 0) := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap v
    simpa using this
  refine ⟨fun i => - f (fun j => if i = j then 1 else 0), fun j => ?_, ?_⟩
  · have hmem : Mᵀ j ∈ cone M := ⟨Pi.single j 1, fun k => by
      by_cases h : k = j
      · subst h; simp
      · simp [h], by ext i; simp [mulVec, dotProduct, Pi.single_apply]⟩
    have := hneg _ hmem
    rw [hf] at this
    simp only [vecMul, dotProduct, transpose_apply] at this ⊢
    have : ∑ x, -f (fun j => if x = j then 1 else 0) * M x j =
        -∑ x, M x j * f (fun j => if x = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith
  · have := hf t
    simp only [dotProduct]
    have : ∑ x, -f (fun j => if x = j then 1 else 0) * t x =
        -∑ x, t x * f (fun j => if x = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith

end ECF

section Upper

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

set_option linter.unusedSectionVars false

lemma ec_le_one (G : Graph V E) (x : E → ℝ) (hx : x ∈ matchingPolyhedron G) (e : E) :
    x e ≤ 1 := by
  obtain ⟨h0, hd, -⟩ := hx
  have hu : (G.ends e).out.1 ∈ G.ends e := Sym2.out_fst_mem _
  calc x e ≤ degSum G x (G.ends e).out.1 := by
        unfold degSum
        exact Finset.single_le_sum (f := x) (fun i _ => h0 i) (by simp [hu])
    _ ≤ 1 := hd _

lemma ec_convex (G : Graph V E) : Convex ℝ (matchingPolyhedron G) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun e => ?_, fun v => ?_, fun S r hr hS => ?_⟩
  · have := hp.1 e; have := hq.1 e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
  · have h1 := hp.2.1 v; have h2 := hq.2.1 v
    have : degSum G (a • p + b • q) v = a * degSum G p v + b * degSum G q v := by
      unfold degSum; simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [this]; nlinarith
  · have h1 := hp.2.2 S r hr hS; have h2 := hq.2.2 S r hr hS
    have : insideSum G (a • p + b • q) S = a * insideSum G p S + b * insideSum G q S := by
      unfold insideSum; simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [this]; nlinarith

lemma ec_degSum_cont (G : Graph V E) (v : V) : Continuous (fun x : E → ℝ => degSum G x v) := by
  unfold degSum
  exact continuous_finset_sum _ (fun e _ => continuous_apply e)

lemma ec_insideSum_cont (G : Graph V E) (S : Finset V) :
    Continuous (fun x : E → ℝ => insideSum G x S) := by
  unfold insideSum
  exact continuous_finset_sum _ (fun e _ => continuous_apply e)

lemma ec_closed (G : Graph V E) : IsClosed (matchingPolyhedron G) := by
  have : matchingPolyhedron G = {x : E → ℝ | ∀ e, 0 ≤ x e} ∩
      ({x | ∀ v : V, degSum G x v ≤ 1} ∩
        {x | ∀ (S : Finset V) (r : ℕ), 1 ≤ r → S.card = 2 * r + 1 → insideSum G x S ≤ (r : ℝ)}) :=
    Set.ext fun x => Iff.rfl
  rw [this]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · rw [Set.setOf_forall]
    exact isClosed_iInter (fun e => isClosed_le continuous_const (continuous_apply e))
  · rw [Set.setOf_forall]
    exact isClosed_iInter (fun v => isClosed_le (ec_degSum_cont G v) continuous_const)
  · rw [Set.setOf_forall]
    refine isClosed_iInter (fun S => ?_)
    rw [Set.setOf_forall]
    refine isClosed_iInter (fun r => ?_)
    by_cases h1 : 1 ≤ r
    · by_cases h2 : S.card = 2 * r + 1
      · simp only [h1, h2, true_implies]
        exact isClosed_le (ec_insideSum_cont G S) continuous_const
      · simp [h2]
    · simp [h1]

lemma ec_compact (G : Graph V E) : IsCompact (matchingPolyhedron G) := by
  apply IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ : E => isCompact_Icc (a := (0:ℝ)) (b := 1)))
    (ec_closed G)
  intro x hx
  rw [Set.mem_univ_pi]
  intro e
  exact ⟨hx.1 e, ec_le_one G x hx e⟩

/-- a matching vector is the incidence vector of a matching -/
lemma ec_mv_matching (G : Graph V E) (c : E → ℝ) (x : E → ℝ) (hx : x ∈ matchingVectors G) :
    IsMatching G (Finset.univ.filter (fun e => x e = 1)) ∧
      W c x = ∑ e ∈ Finset.univ.filter (fun e => x e = 1), c e := by
  obtain ⟨h01, hd⟩ := hx
  have h0 : ∀ g, 0 ≤ x g := fun g => by rcases h01 g with h | h <;> rw [h] <;> norm_num
  constructor
  · intro e he f hf hef v hve hvf
    rw [Finset.mem_filter] at he hf
    have hsub : ({e, f} : Finset E) ⊆ Finset.univ.filter (fun g => v ∈ G.ends g) := by
      intro g hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rw [Finset.mem_filter]
      rcases hg with rfl | rfl
      · exact ⟨Finset.mem_univ _, hve⟩
      · exact ⟨Finset.mem_univ _, hvf⟩
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => h0 g)
    rw [Finset.sum_pair hef, he.2, hf.2] at h1
    have h2 := hd v
    unfold degSum at h2
    linarith
  · unfold W
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    rcases h01 e with h | h <;> simp [h]

lemma ec_W_cont (c : E → ℝ) : Continuous (fun y : E → ℝ => W c y) := by
  unfold W
  exact continuous_finset_sum _ (fun e _ => continuous_const.mul (continuous_apply e))

lemma ec_W_comb (c p q : E → ℝ) (a b : ℝ) : W c (a • p + b • q) = a * W c p + b * W c q := by
  unfold W
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- the linear form is bounded on the polyhedron by the maximum matching weight -/
lemma ec_upper (G : Graph V E) (c : E → ℝ) (L : ℝ)
    (hL : ∀ M : Finset E, IsMatching G M → ∑ e ∈ M, c e ≤ L) :
    ∀ x ∈ matchingPolyhedron G, W c x ≤ L := by
  intro x hx
  have hKM := closure_convexHull_extremePoints (ec_compact G) (ec_convex G)
  rw [theorem_P_vertices_eq_matching_vectors G] at hKM
  rw [← hKM] at hx
  have hclosed : IsClosed {y : E → ℝ | W c y ≤ L} := isClosed_le (ec_W_cont c) continuous_const
  have hconv : Convex ℝ {y : E → ℝ | W c y ≤ L} := by
    intro p hp q hq a b ha hb hab
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [ec_W_comb]
    have h1 : a * W c p ≤ a * L := mul_le_mul_of_nonneg_left hp ha
    have h2 : b * W c q ≤ b * L := mul_le_mul_of_nonneg_left hq hb
    calc a * W c p + b * W c q ≤ a * L + b * L := add_le_add h1 h2
      _ = L := by rw [← add_mul, hab, one_mul]
  have hsub : matchingVectors G ⊆ {y : E → ℝ | W c y ≤ L} := by
    intro y hy
    obtain ⟨hm, hW⟩ := ec_mv_matching G c y hy
    simp only [Set.mem_setOf_eq]
    rw [hW]
    exact hL _ hm
  exact closure_minimal (convexHull_min hsub hconv) hclosed hx

end Upper

section Chain

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

set_option linter.unusedSectionVars false

lemma ec_ends_rep (G : Graph V E) (e : E) : ∃ a b : V, a ≠ b ∧ G.ends e = s(a, b) := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  refine ⟨a, b, ?_, hab.symm⟩
  intro h
  apply G.loopless e
  rw [← hab, h]
  exact Sym2.mk_isDiag_iff.mpr rfl

lemma ec_lift (G : Graph V E) (y : V → ℝ) (e : E) :
    Sym2.lift ⟨fun a b => y a + y b, fun a b => add_comm (y a) (y b)⟩ (G.ends e)
      = ∑ v ∈ Finset.univ.filter (fun v => v ∈ G.ends e), y v := by
  obtain ⟨a, b, hab, he⟩ := ec_ends_rep G e
  rw [he, Sym2.lift_mk]
  have : Finset.univ.filter (fun v => v ∈ s(a, b)) = {a, b} := by
    ext v; simp [Sym2.mem_iff]
  rw [this, Finset.sum_pair hab]

lemma ec_swap {α β : Type*} (A : Finset α) (B : Finset β) (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] (f : α → ℝ) (g : β → ℝ) :
    ∑ a ∈ A, (∑ b ∈ B.filter (fun b => P a b), g b) * f a =
      ∑ b ∈ B, g b * ∑ a ∈ A.filter (fun a => P a b), f a := by
  simp_rw [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

/-- the fundamental identity behind weak duality -/
lemma ec_identity (G : Graph V E) (y : V → ℝ) (z : Finset V → ℝ) (x : E → ℝ) :
    ∑ e, edgeDual G y z e * x e =
      ∑ v, y v * degSum G x v + ∑ S ∈ oddSets, z S * insideSum G x S := by
  unfold edgeDual degSum insideSum
  simp_rw [ec_lift, add_mul, Finset.sum_add_distrib]
  rw [ec_swap Finset.univ Finset.univ (fun e v => v ∈ G.ends e) x y,
    ec_swap Finset.univ oddSets (fun e S => G.ends e ∈ S.sym2) x z]

lemma ec_card_two (S : Finset V) (z : Sym2 V) (hz : ¬ z.IsDiag) (hS : z ∈ S.sym2) :
    (S.filter (fun v => v ∈ z)).card = 2 := by
  induction z using Sym2.ind with
  | h a b =>
    simp only [Sym2.mk_isDiag_iff] at hz
    rw [Finset.mk_mem_sym2_iff] at hS
    have : S.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro (rfl | rfl)
        · exact ⟨hS.1, Or.inl rfl⟩
        · exact ⟨hS.2, Or.inr rfl⟩
    rw [this, Finset.card_pair hz]

lemma ec_mv_sub (G : Graph V E) : matchingVectors G ⊆ matchingPolyhedron G := by
  intro x ⟨h01, hd⟩
  have h0 : ∀ e, 0 ≤ x e := fun e => by rcases h01 e with h | h <;> rw [h] <;> norm_num
  refine ⟨h0, hd, ?_⟩
  intro S r _ hS
  have key : 2 * insideSum G x S ≤ ∑ v ∈ S, degSum G x v := by
    unfold insideSum degSum
    rw [Finset.mul_sum]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro e _
    split_ifs with h
    · rw [← Finset.sum_filter, Finset.sum_const, ec_card_two S _ (G.loopless e) h]
      simp
    · apply Finset.sum_nonneg; intro v _; split_ifs <;> simp [h0 e]
  have hsum : ∑ v ∈ S, degSum G x v ≤ (S.card : ℝ) := by
    calc ∑ v ∈ S, degSum G x v ≤ ∑ v ∈ S, (1:ℝ) := Finset.sum_le_sum (fun v _ => hd v)
      _ = S.card := by simp
  have hk : insideSum G x S =
      (((Finset.univ.filter (fun e => G.ends e ∈ S.sym2)).filter (fun e => x e = 1)).card : ℝ) := by
    unfold insideSum
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e _
    rcases h01 e with h | h <;> simp [h]
  rw [hk] at key ⊢
  rw [hS] at hsum
  set k := ((Finset.univ.filter (fun e => G.ends e ∈ S.sym2)).filter (fun e => x e = 1)).card
  have : (2 * k : ℝ) ≤ 2 * r + 1 := by push_cast at hsum; linarith
  have : 2 * k ≤ 2 * r + 1 := by exact_mod_cast this
  exact_mod_cast (by omega : k ≤ r)

lemma ec_incidence_mv (G : Graph V E) (M : Finset E) (hM : IsMatching G M) :
    incidence M ∈ matchingVectors G := by
  refine ⟨fun e => ?_, fun v => ?_⟩
  · unfold incidence; split_ifs <;> simp
  · unfold degSum incidence
    rw [Finset.sum_boole]
    have : ((Finset.univ.filter (fun e => v ∈ G.ends e)).filter (fun e => e ∈ M)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro e he f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he hf
      by_contra hef
      exact hM e he.2 f hf.2 hef v he.1 hf.1
    exact_mod_cast this

lemma ec_W_incidence (c : E → ℝ) (M : Finset E) : W c (incidence M) = ∑ e ∈ M, c e := by
  unfold W incidence
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma ec_rOf (S : Finset V) (hS : S ∈ oddSets) : ∃ r : ℕ, 1 ≤ r ∧ S.card = 2 * r + 1 ∧
    rOf S = r := by
  classical
  unfold oddSets at hS
  rw [Finset.mem_filter] at hS
  obtain ⟨r, hr, hcard⟩ := hS.2
  refine ⟨r, hr, hcard, ?_⟩
  unfold rOf
  rw [hcard]; push_cast; ring

/-- weak duality with equality forces complementary slackness -/
lemma ec_compslack (G : Graph V E) (c : E → ℝ) (M : Finset E) (hM : IsMatching G M)
    (y : V → ℝ) (z : Finset V → ℝ) (hfeas : DualFeasible G c y z)
    (hU : U y z ≤ ∑ e ∈ M, c e) : CompSlack G c M y z := by
  obtain ⟨hy, hz, hc⟩ := hfeas
  set x := incidence M with hxdef
  have hxM : x ∈ matchingVectors G := ec_incidence_mv G M hM
  have hxC : x ∈ matchingPolyhedron G := ec_mv_sub G hxM
  have hW : W c x = ∑ e ∈ M, c e := ec_W_incidence c M
  have hx0 : ∀ e, 0 ≤ x e := hxC.1
  have hdeg : ∀ v, degSum G x v ≤ 1 := hxC.2.1
  have hins : ∀ S ∈ oddSets, insideSum G x S ≤ rOf S := by
    intro S hS
    obtain ⟨r, hr, hcard, hrOf⟩ := ec_rOf S hS
    rw [hrOf]
    exact hxC.2.2 S r hr hcard
  set A := ∑ e, (edgeDual G y z e - c e) * x e with hA
  set B := ∑ v, y v * (1 - degSum G x v) with hB
  set D := ∑ S ∈ oddSets, z S * (rOf S - insideSum G x S) with hD
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun e _ => mul_nonneg (by linarith [hc e]) (hx0 e))
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun v _ => mul_nonneg (hy v) (by linarith [hdeg v]))
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun S hS => mul_nonneg (hz S hS) (by linarith [hins S hS]))
  have hsum : A + B + D = U y z - ∑ e ∈ M, c e := by
    have hid := ec_identity G y z x
    unfold U
    rw [← hW]
    unfold W
    simp only [hA, hB, hD, sub_mul, mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun e _ => mul_comm (c e) (x e))]
    linarith [hid, Finset.sum_congr (rfl : oddSets = oddSets)
      (fun S _ => mul_comm (rOf S) (z S))]
  have hA' : A = 0 := by linarith
  have hB' : B = 0 := by linarith
  have hD' : D = 0 := by linarith
  rw [hA, Finset.sum_eq_zero_iff_of_nonneg
    (fun e _ => mul_nonneg (by linarith [hc e]) (hx0 e))] at hA'
  rw [hB, Finset.sum_eq_zero_iff_of_nonneg
    (fun v _ => mul_nonneg (hy v) (by linarith [hdeg v]))] at hB'
  rw [hD, Finset.sum_eq_zero_iff_of_nonneg
    (fun S hS => mul_nonneg (hz S hS) (by linarith [hins S hS]))] at hD'
  refine ⟨fun v hv => ?_, fun e he => ?_, fun S hS hzS => ?_⟩
  · have h1 := hB' v (Finset.mem_univ _)
    have h2 : degSum G x v = 0 := by
      unfold degSum
      apply Finset.sum_eq_zero
      intro e he
      rw [Finset.mem_filter] at he
      simp only [hxdef, incidence]
      rw [if_neg]
      intro heM
      exact hv e heM he.2
    rw [h2] at h1
    linarith
  · have h1 := hA' e (Finset.mem_univ _)
    have h2 : x e = 1 := by simp [hxdef, incidence, he]
    rw [h2, mul_one] at h1
    linarith
  · have h1 := hD' S hS
    have h2 : rOf S - insideSum G x S = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exact h
    have h3 : insideSum G x S = ((M.filter (fun e => G.ends e ∈ S.sym2)).card : ℝ) := by
      unfold insideSum
      simp only [hxdef, incidence]
      rw [Finset.sum_boole, Finset.filter_filter]
      congr 2
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [h3] at h2
    linarith

end Chain

section Main

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

set_option linter.unusedSectionVars false

/-- the constraint matrix of the dual program in equality form -/
noncomputable def ecMat (G : Graph V E) : (E ⊕ Unit) → (V ⊕ (Finset V ⊕ (E ⊕ Unit))) → ℝ :=
  fun r cidx => match r, cidx with
  | Sum.inl e, Sum.inl v => if v ∈ G.ends e then 1 else 0
  | Sum.inl e, Sum.inr (Sum.inl S) => if S ∈ oddSets ∧ G.ends e ∈ S.sym2 then 1 else 0
  | Sum.inl e, Sum.inr (Sum.inr (Sum.inl e')) => if e = e' then -1 else 0
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inr _)) => 0
  | Sum.inr _, Sum.inl _ => -1
  | Sum.inr _, Sum.inr (Sum.inl S) => if S ∈ oddSets then -(rOf S) else 0
  | Sum.inr _, Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr _, Sum.inr (Sum.inr (Sum.inr _)) => -1

/-- the right-hand side -/
noncomputable def ecT (c : E → ℝ) (L : ℝ) : (E ⊕ Unit) → ℝ :=
  fun r => match r with
  | Sum.inl e => c e
  | Sum.inr _ => -L

lemma ec_row_e (G : Graph V E) (w : V ⊕ (Finset V ⊕ (E ⊕ Unit)) → ℝ) (e : E) :
    ((ecMat G : Matrix _ _ ℝ) *ᵥ w) (Sum.inl e) =
      ∑ v ∈ Finset.univ.filter (fun v => v ∈ G.ends e), w (Sum.inl v) +
      ∑ S ∈ oddSets.filter (fun S => G.ends e ∈ S.sym2), w (Sum.inr (Sum.inl S)) -
      w (Sum.inr (Sum.inr (Sum.inl e))) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, ecMat]
  simp only [ite_mul, one_mul, zero_mul, neg_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib]
  rw [Finset.sum_filter, Finset.sum_filter]
  have : ∑ S ∈ oddSets, (if G.ends e ∈ S.sym2 then w (Sum.inr (Sum.inl S)) else 0) =
      ∑ S, (if S ∈ oddSets ∧ G.ends e ∈ S.sym2 then w (Sum.inr (Sum.inl S)) else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [this]
  ring

lemma ec_row_u (G : Graph V E) (w : V ⊕ (Finset V ⊕ (E ⊕ Unit)) → ℝ) :
    ((ecMat G : Matrix _ _ ℝ) *ᵥ w) (Sum.inr ()) =
      -(∑ v, w (Sum.inl v)) - ∑ S ∈ oddSets, rOf S * w (Sum.inr (Sum.inl S)) -
      w (Sum.inr (Sum.inr (Sum.inr ()))) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, ecMat]
  simp only [ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_const_zero, add_zero,
    Finset.sum_neg_distrib, Finset.univ_unique, Finset.sum_singleton]
  have : ∑ S, (if S ∈ oddSets then -(rOf S * w (Sum.inr (Sum.inl S))) else 0) =
      -∑ S ∈ oddSets, rOf S * w (Sum.inr (Sum.inl S)) := by
    rw [← Finset.sum_filter, ← Finset.sum_neg_distrib]
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [this]
  ring

lemma ec_col_v (G : Graph V E) (w : E ⊕ Unit → ℝ) (v : V) :
    (w ᵥ* (ecMat G : Matrix _ _ ℝ)) (Sum.inl v) =
      degSum G (fun e => w (Sum.inl e)) v - w (Sum.inr ()) := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, ecMat, degSum]
  simp only [mul_ite, mul_one, mul_zero, mul_neg, Finset.univ_unique, Finset.sum_singleton]
  rw [Finset.sum_filter]
  ring

lemma ec_col_S (G : Graph V E) (w : E ⊕ Unit → ℝ) (S : Finset V) (hS : S ∈ oddSets) :
    (w ᵥ* (ecMat G : Matrix _ _ ℝ)) (Sum.inr (Sum.inl S)) =
      insideSum G (fun e => w (Sum.inl e)) S - rOf S * w (Sum.inr ()) := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, ecMat, insideSum]
  simp only [hS, true_and, mul_ite, mul_one, mul_zero, mul_neg, Finset.univ_unique,
    Finset.sum_singleton, if_true]
  rw [Finset.sum_filter]
  ring

lemma ec_col_e (G : Graph V E) (w : E ⊕ Unit → ℝ) (e : E) :
    (w ᵥ* (ecMat G : Matrix _ _ ℝ)) (Sum.inr (Sum.inr (Sum.inl e))) = -w (Sum.inl e) := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, ecMat]
  simp only [mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.univ_unique, Finset.sum_singleton, Finset.sum_const_zero,
    add_zero]

lemma ec_col_u (G : Graph V E) (w : E ⊕ Unit → ℝ) :
    (w ᵥ* (ecMat G : Matrix _ _ ℝ)) (Sum.inr (Sum.inr (Sum.inr ()))) = -w (Sum.inr ()) := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, ecMat]
  simp only [mul_zero, mul_neg, mul_one, Finset.univ_unique, Finset.sum_singleton,
    Finset.sum_const_zero, zero_add]

lemma ec_dot_t (c : E → ℝ) (L : ℝ) (w : E ⊕ Unit → ℝ) :
    w ⬝ᵥ ecT c L = ∑ e, w (Sum.inl e) * c e - w (Sum.inr ()) * L := by
  simp only [dotProduct, Fintype.sum_sum_type, ecT, Finset.univ_unique, Finset.sum_singleton]
  ring

theorem ec_core (G : Graph V E) (c : E → ℝ) :
    ∃ M : Finset E, IsMatching G M ∧
      ∃ (y : V → ℝ) (z : Finset V → ℝ), DualFeasible G c y z ∧ CompSlack G c M y z := by
  classical
  obtain ⟨M, hMmem, hMmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun M : Finset E => IsMatching G M)) (fun M => ∑ e ∈ M, c e)
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e he => absurd he (Finset.notMem_empty e)⟩⟩
  have hM : IsMatching G M := (Finset.mem_filter.mp hMmem).2
  set L := ∑ e ∈ M, c e with hLdef
  have hL : ∀ M', IsMatching G M' → ∑ e ∈ M', c e ≤ L := fun M' h =>
    hMmax M' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hup := ec_upper G c L hL
  refine ⟨M, hM, ?_⟩
  by_cases hcone : ecT c L ∈ ECF.cone (ecMat G : Matrix _ _ ℝ)
  · obtain ⟨w, hw, hMw0⟩ := hcone
    have hMw : (ecMat G : Matrix _ _ ℝ) *ᵥ w = ecT c L := hMw0
    set y : V → ℝ := fun v => w (Sum.inl v) with hy
    set z : Finset V → ℝ := fun S => w (Sum.inr (Sum.inl S)) with hz
    have hrow : ∀ e, edgeDual G y z e = c e + w (Sum.inr (Sum.inr (Sum.inl e))) := by
      intro e
      have := congrFun hMw (Sum.inl e)
      rw [ec_row_e] at this
      simp only [ecT] at this
      unfold edgeDual
      rw [ec_lift]
      simp only [hy, hz]
      linarith
    have hU : U y z ≤ L := by
      have := congrFun hMw (Sum.inr ())
      rw [ec_row_u] at this
      simp only [ecT] at this
      unfold U
      simp only [hy, hz]
      linarith [hw (Sum.inr (Sum.inr (Sum.inr ())))]
    have hfeas : DualFeasible G c y z :=
      ⟨fun v => hw _, fun S _ => hw _, fun e => by rw [hrow]; linarith [hw (Sum.inr (Sum.inr (Sum.inl e)))]⟩
    exact ⟨y, z, hfeas, ec_compslack G c M hM y z hfeas hU⟩
  · exfalso
    obtain ⟨w, hwM, hwt⟩ := ECF.farkas (ecMat G : Matrix _ _ ℝ) (ecT c L) hcone
    set ξ : E → ℝ := fun e => w (Sum.inl e) with hξ
    set lam := w (Sum.inr ()) with hlam
    have hξ0 : ∀ e, ξ e ≤ 0 := fun e => by
      have := hwM (Sum.inr (Sum.inr (Sum.inl e)))
      rw [ec_col_e] at this
      simp only [hξ]; linarith
    have hlam0 : lam ≤ 0 := by
      have := hwM (Sum.inr (Sum.inr (Sum.inr ())))
      rw [ec_col_u] at this
      linarith
    have hdeg : ∀ v, lam ≤ degSum G ξ v := fun v => by
      have := hwM (Sum.inl v)
      rw [ec_col_v] at this
      linarith
    have hins : ∀ S ∈ oddSets, rOf S * lam ≤ insideSum G ξ S := fun S hS => by
      have := hwM (Sum.inr (Sum.inl S))
      rw [ec_col_S G w S hS] at this
      linarith
    have hobj : ∑ e, ξ e * c e < lam * L := by
      rw [ec_dot_t] at hwt
      linarith
    set x' : E → ℝ := fun e => -ξ e with hx'
    have hx'0 : ∀ e, 0 ≤ x' e := fun e => by simp only [hx']; linarith [hξ0 e]
    have hdeg' : ∀ v, degSum G x' v ≤ -lam := fun v => by
      have := hdeg v
      unfold degSum at this ⊢
      simp only [hx', Finset.sum_neg_distrib]
      linarith
    have hins' : ∀ S ∈ oddSets, insideSum G x' S ≤ rOf S * (-lam) := fun S hS => by
      have := hins S hS
      unfold insideSum at this ⊢
      simp only [hx', Finset.sum_neg_distrib]
      linarith
    have hW' : (-lam) * L < W c x' := by
      unfold W
      simp only [hx', mul_neg, Finset.sum_neg_distrib]
      rw [Finset.sum_congr rfl (fun e _ => mul_comm (c e) (ξ e))]
      linarith
    rcases lt_or_eq_of_le hlam0 with hlt | heq
    · set μ := -lam with hμ
      have hμpos : 0 < μ := by linarith
      set x'' : E → ℝ := fun e => x' e / μ with hx''
      have hx''C : x'' ∈ matchingPolyhedron G := by
        refine ⟨fun e => div_nonneg (hx'0 e) hμpos.le, fun v => ?_, fun S r hr hS => ?_⟩
        · unfold degSum
          simp only [hx'']
          rw [← Finset.sum_div, div_le_one hμpos]
          exact hdeg' v
        · have hSodd : S ∈ oddSets := by
            unfold oddSets
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, r, hr, hS⟩
          have hr' : rOf S = r := by
            unfold rOf; rw [hS]; push_cast; ring
          unfold insideSum
          simp only [hx'']
          rw [← Finset.sum_div, div_le_iff₀ hμpos]
          have := hins' S hSodd
          unfold insideSum at this
          rw [hr'] at this
          linarith
      have := hup x'' hx''C
      unfold W at this
      simp only [hx''] at this
      have hdiv : ∑ e, c e * (x' e / μ) = W c x' / μ := by
        unfold W
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro e _
        ring
      rw [hdiv, div_le_iff₀ hμpos] at this
      linarith
    · rw [heq] at hdeg' hW'
      simp only [neg_zero, zero_mul] at hdeg' hW'
      have hzero : ∀ e, x' e = 0 := by
        intro e
        obtain ⟨a, b, -, hab⟩ := ec_ends_rep G e
        have h1 : x' e ≤ degSum G x' a := by
          unfold degSum
          exact Finset.single_le_sum (f := x') (fun i _ => hx'0 i) (by simp [hab])
        linarith [hx'0 e, hdeg' a]
      have : W c x' = 0 := by
        unfold W
        apply Finset.sum_eq_zero
        intro e _
        rw [hzero e, mul_zero]
      linarith

end Main

end EdmondsMatching65.Polyhedron

open EdmondsMatching65.Polyhedron


theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (c : E → ℝ) :
    ∃ M : Finset E, IsMatching G M ∧
      ∃ (y : V → ℝ) (z : Finset V → ℝ), DualFeasible G c y z ∧ CompSlack G c M y z := by
  exact ec_core G c
