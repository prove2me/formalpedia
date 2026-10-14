-- Prove2me | solution 1 for Disjunctive.Polarity.projection_extreme_rays
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:01:34.473028+00:00
-- url     : https://prove2.me/submissions/c96d7711-5734-4c0f-97bb-977048a6a654

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection



namespace Disjunctive.Polarity

namespace PERfk

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

end PERfk

section PER

open Matrix

variable {m p q : ℕ}

/-- Farkas for `Au ≤ t` with free `u`. -/
lemma per_farkas (A : Matrix (Fin m) (Fin p) ℝ) (t : Fin m → ℝ)
    (h : ¬ ∃ u : Fin p → ℝ, A *ᵥ u ≤ t) :
    ∃ y : Fin m → ℝ, y ᵥ* A = 0 ∧ 0 ≤ y ∧ y ⬝ᵥ t < 0 := by
  let M : Matrix (Fin m) (Fin p ⊕ (Fin p ⊕ Fin m)) ℝ := fun i c => match c with
    | Sum.inl j => A i j
    | Sum.inr (Sum.inl j) => - A i j
    | Sum.inr (Sum.inr k) => if i = k then 1 else 0
  have hnot : t ∉ PERfk.cone M := by
    rintro ⟨z, hz, hMz⟩
    apply h
    refine ⟨fun j => z (Sum.inl j) - z (Sum.inr (Sum.inl j)), fun i => ?_⟩
    have hrow : (M *ᵥ z) i = t i := by rw [← hMz]; rfl
    have hcomp : (M *ᵥ z) i = ∑ j, A i j * z (Sum.inl j) - ∑ j, A i j * z (Sum.inr (Sum.inl j))
        + z (Sum.inr (Sum.inr i)) := by
      simp only [mulVec, dotProduct, Fintype.sum_sum_type, M]
      simp [neg_mul, Finset.sum_neg_distrib, ite_mul]
      ring
    simp only [mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    have := hz (Sum.inr (Sum.inr i))
    linarith
  obtain ⟨y, hy, hyt⟩ := PERfk.farkas M t hnot
  refine ⟨y, ?_, fun k => ?_, hyt⟩
  · funext j
    have h1 := hy (Sum.inl j)
    have h2 := hy (Sum.inr (Sum.inl j))
    simp only [vecMul, dotProduct, M] at h1 h2 ⊢
    have e : ∑ x, y x * -A x j = -∑ x, y x * A x j := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [e] at h2
    change ∑ x, y x * A x j = 0
    linarith
  · have h3 := hy (Sum.inr (Sum.inr k))
    simpa [vecMul, dotProduct, M] using h3

/-- The normalized slice of the projection cone. -/
def perK (A : Matrix (Fin m) (Fin p) ℝ) : Set (Fin m → ℝ) :=
  {v | v ᵥ* A = 0 ∧ 0 ≤ v ∧ ∑ i, v i = 1}

lemma perK_convex (A : Matrix (Fin m) (Fin p) ℝ) : Convex ℝ (perK A) := by
  rintro x ⟨hx1, hx2, hx3⟩ y ⟨hy1, hy2, hy3⟩ a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · rw [add_vecMul, smul_vecMul, smul_vecMul, hx1, hy1, smul_zero, smul_zero, add_zero]
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact add_nonneg (mul_nonneg ha (hx2 i)) (mul_nonneg hb (hy2 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx3, hy3]
    linarith

lemma perK_compact (A : Matrix (Fin m) (Fin p) ℝ) : IsCompact (perK A) := by
  have hcl : IsClosed (perK A) := by
    apply IsClosed.inter
    · apply isClosed_eq _ continuous_const
      exact continuous_id.matrix_vecMul continuous_const
    apply IsClosed.inter
    · exact isClosed_le continuous_const continuous_id
    · apply isClosed_eq _ continuous_const
      fun_prop
  apply (isCompact_Icc (a := (0 : Fin m → ℝ)) (b := 1)).of_isClosed_subset hcl
  rintro v ⟨_, hv2, hv3⟩
  refine ⟨hv2, fun i => ?_⟩
  rw [Pi.one_apply, ← hv3]
  exact Finset.single_le_sum (fun j _ => hv2 j) (Finset.mem_univ i)

lemma per_sum_pos {x : Fin m → ℝ} (hx : 0 ≤ x) (h : ∑ i, x i ≠ 0) : 0 < ∑ i, x i :=
  lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hx i)) (Ne.symm h)

lemma per_zero_of_sum {x : Fin m → ℝ} (hx : 0 ≤ x) (h : ∑ i, x i = 0) : x = 0 := by
  funext i
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hx j)).mp h i (Finset.mem_univ i)

lemma per_normalize (A : Matrix (Fin m) (Fin p) ℝ) {x : Fin m → ℝ}
    (hx : x ∈ ProjectionCone A) (hs : 0 < ∑ i, x i) : (∑ i, x i)⁻¹ • x ∈ perK A := by
  refine ⟨?_, ?_, ?_⟩
  · rw [smul_vecMul, hx.1, smul_zero]
  · exact smul_nonneg (inv_nonneg.mpr hs.le) hx.2
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'

/-- Key step: in an open segment through a point of the ray, the first endpoint is on the ray. -/
lemma per_endpoint (A : Matrix (Fin m) (Fin p) ℝ) {e : Fin m → ℝ}
    (he : e ∈ (perK A).extremePoints ℝ) {x1 x2 : Fin m → ℝ}
    (hx1 : x1 ∈ ProjectionCone A) (hx2 : x2 ∈ ProjectionCone A) {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (ht : 0 ≤ t)
    (hz : a • x1 + b • x2 = t • e) : ∃ s : ℝ, 0 ≤ s ∧ x1 = s • e := by
  have heK := he.1
  have hsum : a * (∑ i, x1 i) + b * (∑ i, x2 i) = t := by
    have := congrArg (fun v : Fin m → ℝ => ∑ i, v i) hz
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, heK.2.2, mul_one] at this
    exact this
  have s1nn : 0 ≤ ∑ i, x1 i := Finset.sum_nonneg (fun i _ => hx1.2 i)
  have s2nn : 0 ≤ ∑ i, x2 i := Finset.sum_nonneg (fun i _ => hx2.2 i)
  by_cases h1 : ∑ i, x1 i = 0
  · exact ⟨0, le_rfl, by rw [per_zero_of_sum hx1.2 h1, zero_smul]⟩
  have s1 := per_sum_pos hx1.2 h1
  by_cases h2 : ∑ i, x2 i = 0
  · have hx2z := per_zero_of_sum hx2.2 h2
    rw [hx2z, smul_zero, add_zero] at hz
    refine ⟨t / a, div_nonneg ht ha.le, ?_⟩
    funext i
    have := congrFun hz i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp
    linarith
  have s2 := per_sum_pos hx2.2 h2
  set S1 := ∑ i, x1 i
  set S2 := ∑ i, x2 i
  have htpos : 0 < t := by rw [← hsum]; positivity
  have hp1 := per_normalize A hx1 s1
  have hp2 := per_normalize A hx2 s2
  have hseg : e ∈ openSegment ℝ (S1⁻¹ • x1) (S2⁻¹ • x2) := by
    refine ⟨a * S1 / t, b * S2 / t, by positivity, by positivity, ?_, ?_⟩
    · rw [← add_div, hsum, div_self htpos.ne']
    · funext i
      have := congrFun hz i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      field_simp
      linarith
  have := ((mem_extremePoints.mp he).2 _ hp1 _ hp2 hseg).1
  refine ⟨S1, s1.le, ?_⟩
  rw [← this, smul_smul, mul_inv_cancel₀ s1.ne', one_smul]

lemma per_extreme_ray (A : Matrix (Fin m) (Fin p) ℝ) {e : Fin m → ℝ}
    (he : e ∈ (perK A).extremePoints ℝ) : IsExtremeRay (ProjectionCone A) e := by
  have heK := he.1
  have heW : e ∈ ProjectionCone A := ⟨heK.1, heK.2.1⟩
  refine ⟨?_, heW, ?_, ?_⟩
  · intro h0
    have := heK.2.2
    rw [h0] at this
    simp at this
  · rintro _ ⟨t, ht, rfl⟩
    constructor
    · rw [smul_vecMul, heK.1, smul_zero]
    · exact smul_nonneg ht heK.2.1
  · intro x1 hx1 x2 hx2 z hz hseg
    obtain ⟨t, ht, rfl⟩ := hz
    obtain ⟨a, b, ha, hb, hab, hab'⟩ := hseg
    obtain ⟨s1, hs1, e1⟩ := per_endpoint A he hx1 hx2 ha hb hab ht hab'
    exact ⟨s1, hs1, e1⟩

theorem projection_extreme_rays_core (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) :
    ProjOntoX (Poly2 A B b) =
      {x : Fin q → ℝ | ∀ v, IsExtremeRay (ProjectionCone A) v →
        dotProduct (Matrix.vecMul v B) x ≤ dotProduct v b} := by
  ext x
  constructor
  · rintro ⟨u, hu⟩ v ⟨_, ⟨hvA, hv0⟩, _⟩
    have hu' : A *ᵥ u + B *ᵥ x ≤ b := hu
    have h1 : v ⬝ᵥ (A *ᵥ u + B *ᵥ x) ≤ v ⬝ᵥ b := by
      simp only [dotProduct]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hu' i) (hv0 i))
    rw [dotProduct_add, dotProduct_mulVec, dotProduct_mulVec, hvA, zero_dotProduct,
      zero_add] at h1
    exact h1
  · intro hx
    by_contra hnot
    have hno : ¬ ∃ u : Fin p → ℝ, A *ᵥ u ≤ b - B *ᵥ x := by
      rintro ⟨u, hu⟩
      apply hnot
      refine ⟨u, ?_⟩
      show A *ᵥ u + B *ᵥ x ≤ b
      intro i
      have := hu i
      simp only [Pi.sub_apply] at this
      simp only [Pi.add_apply]
      linarith
    obtain ⟨y, hyA, hy0, hyt⟩ := per_farkas A _ hno
    have hyW : y ∈ ProjectionCone A := ⟨hyA, hy0⟩
    have hs : ∑ i, y i ≠ 0 := by
      intro h
      rw [per_zero_of_sum hy0 h, zero_dotProduct] at hyt
      exact lt_irrefl _ hyt
    have hspos := per_sum_pos hy0 hs
    have hyK := per_normalize A hyW hspos
    have hKM := closure_convexHull_extremePoints (perK_compact A) (perK_convex A)
    let H : Set (Fin m → ℝ) := {v | 0 ≤ v ⬝ᵥ (b - B *ᵥ x)}
    have hHc : IsClosed H := isClosed_le continuous_const (by simp only [dotProduct]; fun_prop)
    have hHv : Convex ℝ H := convex_halfSpace_ge
      ⟨fun v w => add_dotProduct v w _, fun c v => smul_dotProduct c v _⟩ 0
    have hext : (perK A).extremePoints ℝ ⊆ H := by
      intro v hv
      have := hx v (per_extreme_ray A hv)
      show 0 ≤ v ⬝ᵥ (b - B *ᵥ x)
      rw [dotProduct_sub, dotProduct_mulVec]
      linarith
    have hsub : perK A ⊆ H := by
      rw [← hKM]
      exact closure_minimal (convexHull_min hext hHv) hHc
    have := hsub hyK
    simp only [H, Set.mem_setOf_eq, smul_dotProduct, smul_eq_mul] at this
    have := (mul_nonneg_iff_of_pos_left (inv_pos.mpr hspos)).mp this
    linarith

end PER

end Disjunctive.Polarity

open Disjunctive.Polarity


theorem solution {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) :
    ProjOntoX (Poly2 A B b) =
      {x : Fin q → ℝ | ∀ v, IsExtremeRay (ProjectionCone A) v →
        dotProduct (Matrix.vecMul v B) x ≤ dotProduct v b} := by
  exact projection_extreme_rays_core A B b
