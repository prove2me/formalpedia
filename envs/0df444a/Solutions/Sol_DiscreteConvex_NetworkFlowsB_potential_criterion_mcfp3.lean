-- Prove2me | solution 1 for DiscreteConvex.NetworkFlowsB.potential_criterion_mcfp3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:13:37.564979+00:00
-- url     : https://prove2.me/submissions/50970c94-b781-4be9-960f-4023d8e5d106

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvexArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotential

open Classical
open scoped Pointwise

namespace DiscreteConvex.NetworkFlowsB

namespace PCFarkas

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

lemma colLI_unique (M : Matrix κ ι ℝ) (z1 z2 : ι → ℝ) (h : supp z1 = supp z2)
    (hli : ColLI M (supp z1)) (hM : M *ᵥ z1 = M *ᵥ z2) : z1 = z2 := by
  have hw : ∀ j, j ∉ supp z1 → (z1 - z2) j = 0 := by
    intro j hj
    have hj2 : j ∉ supp z2 := h ▸ hj
    rw [mem_supp, not_not] at hj hj2
    simp [hj, hj2]
  have hsum := sum_sub_eq_mulVec M (supp z1) (z1 - z2) hw
  rw [mulVec_sub, hM, sub_self] at hsum
  have := Fintype.linearIndependent_iff.mp hli (fun j => (z1 - z2) j) hsum
  funext j
  by_cases hj : j ∈ supp z1
  · have := this ⟨j, hj⟩; simp only [Pi.sub_apply] at this; linarith
  · have := hw j hj; simp only [Pi.sub_apply] at this; linarith

lemma attain (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (L : ℝ)
    (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z) (z0 : ι → ℝ) (hz0 : PFeas M r z0) :
    ∃ zs, PFeas M r zs ∧ ColLI M (supp zs) ∧ ∀ z, PFeas M r z → c ⬝ᵥ zs ≤ c ⬝ᵥ z := by
  let F : Set (ι → ℝ) := {z | PFeas M r z ∧ ColLI M (supp z)}
  have hinj : Set.InjOn supp F := by
    intro z1 h1 z2 h2 h
    exact colLI_unique M z1 z2 h h1.2 (by rw [h1.1.2, h2.1.2])
  have hfin : F.Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  obtain ⟨z1, hz1, _, _, hz1li⟩ := reduce M r c L hL _ z0 rfl hz0
  obtain ⟨zs, hzs, hmin⟩ := Set.exists_min_image F (fun z => c ⬝ᵥ z) hfin ⟨z1, hz1, hz1li⟩
  refine ⟨zs, hzs.1, hzs.2, fun z hz => ?_⟩
  obtain ⟨z', hz', hc', _, hli'⟩ := reduce M r c L hL _ z rfl hz
  exact le_trans (hmin z' ⟨hz', hli'⟩) hc'


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

end PCFarkas

section PC
set_option linter.unusedSectionVars false

lemma farkasL {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (L : κ → (ι → ℝ) →ₗ[ℝ] ℝ) (c : (ι → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ d, (∀ k, L k d ≤ 0) → 0 ≤ c d) :
    ∃ lam : κ → ℝ, (∀ k, 0 ≤ lam k) ∧ ∀ z, c z = - ∑ k, lam k * L k z := by
  have hlin : ∀ (g : (ι → ℝ) →ₗ[ℝ] ℝ) (z : ι → ℝ),
      g z = ∑ i, z i * g (fun j => if i = j then 1 else 0) := by
    intro g z
    have := LinearMap.pi_apply_eq_sum_univ g z
    simpa using this
  let M : Matrix ι κ ℝ := fun i k => - L k (fun j => if i = j then 1 else 0)
  let t : ι → ℝ := fun i => c (fun j => if i = j then 1 else 0)
  by_cases ht : t ∈ PCFarkas.cone M
  · obtain ⟨w, hw, hMw⟩ := ht
    refine ⟨w, hw, fun z => ?_⟩
    have hti : ∀ i, t i = ∑ k, M i k * w k := fun i => by
      rw [← hMw]; simp [Matrix.mulVec, dotProduct]
    rw [hlin c z]
    simp_rw [hlin (L _) z]
    calc ∑ i, z i * c (fun j => if i = j then 1 else 0) = ∑ i, z i * t i := rfl
      _ = ∑ i, z i * ∑ k, M i k * w k := by simp_rw [hti]
      _ = _ := by
        simp only [M, Finset.mul_sum]
        rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
  · exfalso
    obtain ⟨y, hy, hyt⟩ := PCFarkas.farkas M t ht
    have h1 : ∀ k, L k y ≤ 0 := by
      intro k
      have := hy k
      simp only [Matrix.vecMul, dotProduct, M] at this
      rw [hlin (L k) y]
      have e : ∑ x, y x * -(L k) (fun j => if x = j then 1 else 0) =
          -∑ x, y x * (L k) (fun j => if x = j then 1 else 0) := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      linarith
    have h2 : c y < 0 := by
      rw [hlin c y]; simpa [dotProduct, t] using hyt
    linarith [h y h1]

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma bnd_pair (tail head : A → V) (q : V → ℝ) (xi : A → ℝ) :
    ∑ v, q v * Boundary tail head xi v = ∑ a, xi a * Coboundary tail head q a := by
  have h1 : ∀ g : A → V, ∑ v, q v * ∑ a, (if g a = v then xi a else 0) = ∑ a, xi a * q (g a) := by
    intro g
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp only [Boundary, Coboundary, Finset.sum_filter, mul_sub, Finset.sum_sub_distrib, h1]

abbrev Iota (V A : Type*) := A ⊕ A ⊕ Option V

def mkv (xi s : A → ℝ) (y : V → ℝ) (r : ℝ) : Iota V A → ℝ
  | .inl a => xi a
  | .inr (.inl a) => s a
  | .inr (.inr (some v)) => y v
  | .inr (.inr none) => r

def PP (i : Iota V A) : (Iota V A → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i

@[simp] lemma PP_apply (i : Iota V A) (z : Iota V A → ℝ) : PP i z = z i := rfl

def Lbd (tail head : A → V) (v : V) : (Iota V A → ℝ) →ₗ[ℝ] ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => tail a = v), PP (.inl a) -
    ∑ a ∈ Finset.univ.filter (fun a => head a = v), PP (.inl a)

lemma Lbd_apply (tail head : A → V) (v : V) (z : Iota V A → ℝ) :
    Lbd tail head v z = Boundary tail head (fun a => z (.inl a)) v := by
  simp [Lbd, Boundary, LinearMap.sub_apply, LinearMap.sum_apply]

abbrev Kap (V A : Type*) (m : ℕ) (ma : A → ℕ) := (Σ a, Fin (ma a)) ⊕ Fin m ⊕ V ⊕ V

def Lall (tail head : A → V) (m : ℕ) (C : Fin m → Option V → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) : Kap V A m ma → (Iota V A → ℝ) →ₗ[ℝ] ℝ
  | .inl ⟨a, j⟩ => Ca a j false • PP (.inl a) + Ca a j true • PP (.inr (.inl a))
  | .inr (.inl i) => C i none • PP (.inr (.inr none)) + ∑ v, C i (some v) • PP (.inr (.inr (some v)))
  | .inr (.inr (.inl v)) => PP (.inr (.inr (some v))) - Lbd tail head v
  | .inr (.inr (.inr v)) => Lbd tail head v - PP (.inr (.inr (some v)))

def ball (m : ℕ) (B : Fin m → ℝ) (ma : A → ℕ) (Ba : ∀ a, Fin (ma a) → ℝ) :
    Kap V A m ma → ℝ
  | .inl ⟨a, j⟩ => Ba a j
  | .inr (.inl i) => B i
  | .inr (.inr _) => 0

def cobj : (Iota V A → ℝ) →ₗ[ℝ] ℝ := ∑ a, PP (.inr (.inl a)) + PP (.inr (.inr none))

lemma cobj_apply (z : Iota V A → ℝ) :
    (cobj : (Iota V A → ℝ) →ₗ[ℝ] ℝ) z = ∑ a, z (.inr (.inl a)) + z (.inr (.inr none)) := by
  simp [cobj, LinearMap.sum_apply]

lemma Lall_arc (tail head : A → V) (m : ℕ) (C : Fin m → Option V → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) (a : A) (j : Fin (ma a)) (z : Iota V A → ℝ) :
    Lall tail head m C ma Ca (.inl ⟨a, j⟩) z = Ca a j false * z (.inl a) + Ca a j true * z (.inr (.inl a)) := by
  simp [Lall]

lemma Lall_f (tail head : A → V) (m : ℕ) (C : Fin m → Option V → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) (i : Fin m) (z : Iota V A → ℝ) :
    Lall tail head m C ma Ca (.inr (.inl i)) z =
      C i none * z (.inr (.inr none)) + ∑ v, C i (some v) * z (.inr (.inr (some v))) := by
  simp [Lall, LinearMap.sum_apply]

lemma Lall_e1 (tail head : A → V) (m : ℕ) (C : Fin m → Option V → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) (v : V) (z : Iota V A → ℝ) :
    Lall tail head m C ma Ca (.inr (.inr (.inl v))) z =
      z (.inr (.inr (some v))) - Boundary tail head (fun a => z (.inl a)) v := by
  simp [Lall, Lbd_apply]

lemma Lall_e2 (tail head : A → V) (m : ℕ) (C : Fin m → Option V → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) (v : V) (z : Iota V A → ℝ) :
    Lall tail head m C ma Ca (.inr (.inr (.inr v))) z =
      Boundary tail head (fun a => z (.inl a)) v - z (.inr (.inr (some v))) := by
  simp [Lall, Lbd_apply]


lemma sum_update_mul_sub (g w : A → ℝ) (a : A) (u : ℝ) :
    ∑ x, Function.update g a u x * w x - ∑ x, g x * w x = (u - g a) * w a := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
  · simp; ring
  · intro b _ hb; simp [Function.update_of_ne hb]
  · simp

lemma sum_update_sub (g : A → ℝ) (a : A) (u : ℝ) :
    ∑ x, Function.update g a u x - ∑ x, g x = u - g a := by
  have := sum_update_mul_sub g (fun _ => 1) a u
  simpa using this

lemma feas_vals (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) (hfeas : FeasibleFlowMCFP3 tail head fa f xi) :
    ∃ u : A → ℝ, ∃ w : ℝ, (∀ a, fa a (xi a) = (u a : WithTop ℝ)) ∧
      f (Boundary tail head xi) = (w : WithTop ℝ) :=
  ⟨fun a => (fa a (xi a)).untop (hfeas.1 a), (f _).untop hfeas.2,
    fun a => (WithTop.coe_untop _ _).symm, (WithTop.coe_untop _ _).symm⟩

lemma gam_eq (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) (u : A → ℝ) (w : ℝ) (hu : ∀ a, fa a (xi a) = (u a : WithTop ℝ))
    (hw : f (Boundary tail head xi) = (w : WithTop ℝ)) :
    Gamma3 tail head fa f xi = ((∑ a, u a + w : ℝ) : WithTop ℝ) := by
  unfold Gamma3
  simp only [hu, hw]
  push_cast
  rfl

lemma pot_ineq (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (p : V → ℝ) (xi xi' u u' : A → ℝ) (w w' : ℝ)
    (hu : ∀ a, fa a (xi a) = (u a : WithTop ℝ)) (hu' : ∀ a, fa a (xi' a) = (u' a : WithTop ℝ))
    (hw : f (Boundary tail head xi) = (w : WithTop ℝ))
    (hw' : f (Boundary tail head xi') = (w' : WithTop ℝ))
    (hp : IsOptimalPotential tail head fa f xi p) :
    (∀ a, u a + Coboundary tail head p a * xi a ≤ u' a + Coboundary tail head p a * xi' a) ∧
      w - ∑ v, p v * Boundary tail head xi v ≤ w' - ∑ v, p v * Boundary tail head xi' v := by
  constructor
  · intro a
    have := hp.1 a (xi' a)
    simp only [ReducedArcCost, hu, hu'] at this
    exact_mod_cast this
  · have := hp.2 (Boundary tail head xi')
    simp only [ReducedBoundaryCost, hw, hw'] at this
    exact_mod_cast this

lemma easy_dir (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) (p : V → ℝ) (hfeas : FeasibleFlowMCFP3 tail head fa f xi)
    (hp : IsOptimalPotential tail head fa f xi p) : OptimalFlowMCFP3 tail head fa f xi := by
  refine ⟨hfeas, fun xi' hf' => ?_⟩
  obtain ⟨u, w, hu, hw⟩ := feas_vals tail head fa f xi hfeas
  obtain ⟨u', w', hu', hw'⟩ := feas_vals tail head fa f xi' hf'
  obtain ⟨h1, h2⟩ := pot_ineq tail head fa f p xi xi' u u' w w' hu hu' hw hw' hp
  rw [gam_eq tail head fa f xi u w hu hw, gam_eq tail head fa f xi' u' w' hu' hw', WithTop.coe_le_coe]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => h1 a)
  simp only [Finset.sum_add_distrib] at hs
  have e1 := bnd_pair tail head p xi
  have e2 := bnd_pair tail head p xi'
  have e3 : ∑ a, Coboundary tail head p a * xi a = ∑ a, xi a * Coboundary tail head p a :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have e4 : ∑ a, Coboundary tail head p a * xi' a = ∑ a, xi' a * Coboundary tail head p a :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  linarith

lemma transfer_dir (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) (p : V → ℝ) (ho : OptimalFlowMCFP3 tail head fa f xi)
    (hp : IsOptimalPotential tail head fa f xi p) (xi' : A → ℝ)
    (ho' : OptimalFlowMCFP3 tail head fa f xi') : IsOptimalPotential tail head fa f xi' p := by
  obtain ⟨u, w, hu, hw⟩ := feas_vals tail head fa f xi ho.1
  obtain ⟨u', w', hu', hw'⟩ := feas_vals tail head fa f xi' ho'.1
  obtain ⟨h1, h2⟩ := pot_ineq tail head fa f p xi xi' u u' w w' hu hu' hw hw' hp
  have g1 := ho.2 xi' ho'.1
  have g2 := ho'.2 xi ho.1
  rw [gam_eq tail head fa f xi u w hu hw, gam_eq tail head fa f xi' u' w' hu' hw',
    WithTop.coe_le_coe] at g1 g2
  have e1 := bnd_pair tail head p xi
  have e2 := bnd_pair tail head p xi'
  have hS : ∑ a, ((u' a + Coboundary tail head p a * xi' a) -
      (u a + Coboundary tail head p a * xi a)) =
      (∑ a, u' a + ∑ a, xi' a * Coboundary tail head p a) -
        (∑ a, u a + ∑ a, xi a * Coboundary tail head p a) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have e3 : ∑ a, Coboundary tail head p a * xi a = ∑ a, xi a * Coboundary tail head p a :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    have e4 : ∑ a, Coboundary tail head p a * xi' a = ∑ a, xi' a * Coboundary tail head p a :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [e3, e4]
  have hnn : ∀ a ∈ Finset.univ, 0 ≤ (u' a + Coboundary tail head p a * xi' a) -
      (u a + Coboundary tail head p a * xi a) := fun a _ => by linarith [h1 a]
  have hS0 : ∑ a, ((u' a + Coboundary tail head p a * xi' a) -
      (u a + Coboundary tail head p a * xi a)) = 0 := by
    have := Finset.sum_nonneg hnn
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hS0
  constructor
  · intro a t
    have heq : ReducedArcCost tail head fa p a (xi' a) = ReducedArcCost tail head fa p a (xi a) := by
      simp only [ReducedArcCost, hu, hu']
      have := hz a (Finset.mem_univ a)
      have h' : u' a + Coboundary tail head p a * xi' a = u a + Coboundary tail head p a * xi a := by
        linarith
      exact_mod_cast congrArg (fun x : ℝ => (x : WithTop ℝ)) h'
    rw [heq]; exact hp.1 a t
  · intro y
    have heq : ReducedBoundaryCost f p (Boundary tail head xi') =
        ReducedBoundaryCost f p (Boundary tail head xi) := by
      simp only [ReducedBoundaryCost, hw, hw']
      have := Finset.sum_nonneg hnn
      have h' : w' - ∑ v, p v * Boundary tail head xi' v = w - ∑ v, p v * Boundary tail head xi v := by
        linarith
      exact_mod_cast congrArg (fun x : ℝ => (x : WithTop ℝ)) h'
    rw [heq]; exact hp.2 y


theorem hard_core (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (m : ℕ) (C : Fin m → Option V → ℝ) (B : Fin m → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) (Ba : ∀ a, Fin (ma a) → ℝ)
    (hC : ∀ (y : V → ℝ) (r : ℝ), f y ≤ (r : WithTop ℝ) ↔
      ∀ i, C i none * r + ∑ v, C i (some v) * y v ≤ B i)
    (hCa : ∀ a (t s : ℝ), fa a t ≤ (s : WithTop ℝ) ↔
      ∀ j, Ca a j false * t + Ca a j true * s ≤ Ba a j)
    (xi : A → ℝ) (hopt : OptimalFlowMCFP3 tail head fa f xi) :
    ∃ p, IsOptimalPotential tail head fa f xi p := by
  obtain ⟨hfeas, hmin⟩ := hopt
  have lp_flow : ∀ z : Iota V A → ℝ, (∀ k, Lall tail head m C ma Ca k z ≤ ball m B ma Ba k) →
      FeasibleFlowMCFP3 tail head fa f (fun a => z (.inl a)) ∧
      Gamma3 tail head fa f (fun a => z (.inl a)) ≤ ((cobj z : ℝ) : WithTop ℝ) := by
    intro z hz
    have harc : ∀ a, fa a (z (.inl a)) ≤ ((z (.inr (.inl a)) : ℝ) : WithTop ℝ) := by
      intro a; rw [hCa]; intro j; have := hz (.inl ⟨a, j⟩)
      rw [Lall_arc] at this; simp only [ball] at this; linarith
    have hy : (fun v => z (.inr (.inr (some v)))) = Boundary tail head (fun a => z (.inl a)) := by
      funext v
      have h1 := hz (.inr (.inr (.inl v))); have h2 := hz (.inr (.inr (.inr v)))
      rw [Lall_e1] at h1; rw [Lall_e2] at h2
      simp only [ball] at h1 h2; linarith
    have hfz : f (Boundary tail head (fun a => z (.inl a))) ≤
        ((z (.inr (.inr none)) : ℝ) : WithTop ℝ) := by
      rw [← hy, hC]; intro i; have := hz (.inr (.inl i))
      rw [Lall_f] at this; simp only [ball] at this; linarith
    refine ⟨⟨fun a => ne_top_of_le_ne_top WithTop.coe_ne_top (harc a),
      ne_top_of_le_ne_top WithTop.coe_ne_top hfz⟩, ?_⟩
    rw [cobj_apply]; unfold Gamma3
    push_cast
    exact add_le_add (Finset.sum_le_sum (fun a _ => harc a)) hfz
  obtain ⟨sS, rS, hsS, hrS⟩ := feas_vals tail head fa f xi hfeas
  set zS : Iota V A → ℝ := mkv xi sS (Boundary tail head xi) rS with hzSdef
  have hzS : ∀ k, Lall tail head m C ma Ca k zS ≤ ball m B ma Ba k := by
    rintro (⟨a, j⟩ | i | v | v)
    · rw [Lall_arc]; simp only [zS, mkv, ball]
      have := (hCa a _ _).1 (le_of_eq (hsS a)) j; linarith
    · rw [Lall_f]; simp only [zS, mkv, ball]
      have := (hC _ _).1 (le_of_eq hrS) i; linarith
    · rw [Lall_e1]; simp [zS, mkv, ball]
    · rw [Lall_e2]; simp [zS, mkv, ball]
  have hgam : Gamma3 tail head fa f xi = ((cobj zS : ℝ) : WithTop ℝ) := by
    rw [gam_eq tail head fa f xi sS rS hsS hrS, cobj_apply]
    simp [zS, mkv]
  have hnoimp : ∀ d, (∀ k, (if Lall tail head m C ma Ca k zS = ball m B ma Ba k
      then Lall tail head m C ma Ca k else 0) d ≤ 0) → 0 ≤ (cobj : (Iota V A → ℝ) →ₗ[ℝ] ℝ) d := by
    intro d hd
    by_contra hneg; push_neg at hneg
    have hev : ∀ k, ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
        Lall tail head m C ma Ca k (zS + ε • d) ≤ ball m B ma Ba k := by
      intro k
      have hlin : ∀ ε : ℝ, Lall tail head m C ma Ca k (zS + ε • d) =
          Lall tail head m C ma Ca k zS + ε * Lall tail head m C ma Ca k d := by
        intro ε; simp [map_add, map_smul]
      simp_rw [hlin]
      by_cases hk : Lall tail head m C ma Ca k zS = ball m B ma Ba k
      · have := hd k; rw [if_pos hk] at this
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [hk]; nlinarith [Set.mem_Ioi.mp hε]
      · have hlt : Lall tail head m C ma Ca k zS < ball m B ma Ba k := lt_of_le_of_ne (hzS k) hk
        have hc : Continuous (fun ε : ℝ => Lall tail head m C ma Ca k zS +
            ε * Lall tail head m C ma Ca k d) := by fun_prop
        have ht := hc.tendsto 0
        simp only [zero_mul, add_zero] at ht
        exact ((ht.eventually (gt_mem_nhds hlt)).mono fun ε h => h.le).filter_mono
          nhdsWithin_le_nhds
    have hall := Filter.eventually_all.2 hev
    obtain ⟨ε, hε, hεpos⟩ := (hall.and self_mem_nhdsWithin).exists
    obtain ⟨hF, hG⟩ := lp_flow _ hε
    have h1 := hmin _ hF
    have hxi : (fun a => (zS + ε • d) (.inl a)) = fun a => xi a + ε * d (.inl a) := by
      funext a; simp [zS, mkv]
    rw [hgam] at h1
    have h2 := h1.trans hG
    rw [WithTop.coe_le_coe, map_add, map_smul, smul_eq_mul] at h2
    have hε0 : (0:ℝ) < ε := hεpos
    nlinarith
  obtain ⟨lam, hlam0, hid⟩ := farkasL _ _ hnoimp
  set lam' : Kap V A m ma → ℝ := fun k =>
    if Lall tail head m C ma Ca k zS = ball m B ma Ba k then lam k else 0 with hlam'
  have hid' : ∀ z, (cobj : (Iota V A → ℝ) →ₗ[ℝ] ℝ) z =
      - ∑ k, lam' k * Lall tail head m C ma Ca k z := by
    intro z; rw [hid z]; congr 1; refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : Lall tail head m C ma Ca k zS = ball m B ma Ba k <;> simp [lam', hk]
  have hl0 : ∀ k, 0 ≤ lam' k := by
    intro k; by_cases hk : Lall tail head m C ma Ca k zS = ball m B ma Ba k <;>
      simp [lam', hk, hlam0 k]
  have hact : ∀ k, lam' k ≠ 0 → Lall tail head m C ma Ca k zS = ball m B ma Ba k := by
    intro k hk; by_contra h; exact hk (by simp [lam', h])
  have key : ∀ z : Iota V A → ℝ,
      (∀ x, Lall tail head m C ma Ca (Sum.inl x : Kap V A m ma) z ≤
        ball m B ma Ba (Sum.inl x : Kap V A m ma)) →
      (∀ i, Lall tail head m C ma Ca (Sum.inr (Sum.inl i) : Kap V A m ma) z ≤
        ball m B ma Ba (Sum.inr (Sum.inl i) : Kap V A m ma)) →
      cobj zS - cobj z ≤
        ∑ v, lam' (.inr (.inr (.inl v))) * (Lall tail head m C ma Ca (.inr (.inr (.inl v))) z -
          Lall tail head m C ma Ca (.inr (.inr (.inl v))) zS) +
        ∑ v, lam' (.inr (.inr (.inr v))) * (Lall tail head m C ma Ca (.inr (.inr (.inr v))) z -
          Lall tail head m C ma Ca (.inr (.inr (.inr v))) zS) := by
    intro z hz1 hz2
    have he : cobj zS - cobj z = ∑ k, lam' k * (Lall tail head m C ma Ca k z -
        Lall tail head m C ma Ca k zS) := by
      rw [hid', hid']; simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [he, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have hterm : ∀ k, Lall tail head m C ma Ca k z ≤ ball m B ma Ba k →
        lam' k * (Lall tail head m C ma Ca k z - Lall tail head m C ma Ca k zS) ≤ 0 := by
      intro k hk
      by_cases h0 : lam' k = 0
      · simp [h0]
      · rw [hact k h0]; exact mul_nonpos_of_nonneg_of_nonpos (hl0 k) (by linarith)
    have e1 := Finset.sum_nonpos (fun x (_ : x ∈ Finset.univ) => hterm _ (hz1 x))
    have e2 := Finset.sum_nonpos (fun x (_ : x ∈ Finset.univ) => hterm _ (hz2 x))
    linarith
  refine ⟨fun v => lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v))), ?_, ?_⟩
  · intro a t
    simp only [ReducedArcCost]
    rw [hsS a]
    cases hft : fa a t with
    | top => simp
    | coe s =>
      set z : Iota V A → ℝ := mkv (Function.update xi a t) (Function.update sS a s)
        (Boundary tail head xi) rS with hzdef
      have hk := key z (by
        rintro ⟨a', j⟩
        rw [Lall_arc]; simp only [ball]
        by_cases ha : a' = a
        · subst ha
          simp only [z, mkv, Function.update_self]
          have := (hCa a' t s).1 (le_of_eq hft) j; linarith
        · simp only [z, mkv, Function.update_of_ne ha]
          have := hzS (.inl ⟨a', j⟩); rw [Lall_arc] at this; simpa [zS, mkv, ball] using this)
        (by
          intro i
          have := hzS (.inr (.inl i)); rw [Lall_f] at this ⊢; simpa [z, zS, mkv] using this)
      simp only [Lall_e1, Lall_e2, cobj_apply, z, zS, mkv] at hk
      have hc : ∑ x, Function.update sS a s x - ∑ x, sS x = s - sS a := sum_update_sub sS a s
      have hb : ∑ v, (lam' (.inr (.inr (.inl v))) *
            (Boundary tail head xi v - Boundary tail head (fun a_1 => Function.update xi a t a_1) v -
              (Boundary tail head xi v - Boundary tail head xi v)) +
          lam' (.inr (.inr (.inr v))) *
            (Boundary tail head (fun a_1 => Function.update xi a t a_1) v - Boundary tail head xi v -
              (Boundary tail head xi v - Boundary tail head xi v))) =
          ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) *
            Boundary tail head (Function.update xi a t) v -
          ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) *
            Boundary tail head xi v := by
        rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun v _ => ?_); ring
      rw [← Finset.sum_add_distrib, hb, bnd_pair, bnd_pair,
        sum_update_mul_sub] at hk
      have : sS a + Coboundary tail head
          (fun v => lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) a * xi a ≤
          s + Coboundary tail head
          (fun v => lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) a * t := by
        nlinarith
      exact_mod_cast this
  · intro y
    simp only [ReducedBoundaryCost]
    rw [hrS]
    cases hfy : f y with
    | top => simp
    | coe r =>
      set z : Iota V A → ℝ := mkv xi sS y r with hzdef
      have hk := key z (by
        rintro ⟨a', j⟩
        have := hzS (.inl ⟨a', j⟩); rw [Lall_arc] at this ⊢; simpa [z, zS, mkv] using this)
        (by
          intro i
          rw [Lall_f]; simp only [ball, z, mkv]
          have := (hC y r).1 (le_of_eq hfy) i; linarith)
      simp only [Lall_e1, Lall_e2, cobj_apply, z, zS, mkv] at hk
      rw [← Finset.sum_add_distrib] at hk
      have hb : ∑ v, (lam' (.inr (.inr (.inl v))) *
            (y v - Boundary tail head xi v - (Boundary tail head xi v - Boundary tail head xi v)) +
          lam' (.inr (.inr (.inr v))) *
            (Boundary tail head xi v - y v - (Boundary tail head xi v - Boundary tail head xi v))) =
          ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) *
            Boundary tail head xi v -
          ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) * y v := by
        rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun v _ => ?_); ring
      rw [hb] at hk
      have : rS - ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) *
            Boundary tail head xi v ≤
          r - ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) * y v := by
        linarith
      exact_mod_cast this


theorem potential_criterion_mcfp3_core (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (hf : IsPolyhedralConvex f) (hfa : ∀ a, IsPolyhedralConvexArc (fa a)) :
    (∀ xi, FeasibleFlowMCFP3 tail head fa f xi →
      (OptimalFlowMCFP3 tail head fa f xi ↔ ∃ p : V → ℝ, IsOptimalPotential tail head fa f xi p)) ∧
    (∀ xi p, OptimalFlowMCFP3 tail head fa f xi → IsOptimalPotential tail head fa f xi p →
      ∀ xi', FeasibleFlowMCFP3 tail head fa f xi' →
        (OptimalFlowMCFP3 tail head fa f xi' ↔ IsOptimalPotential tail head fa f xi' p)) := by
  obtain ⟨m, C, B, hS⟩ := hf
  choose ma Ca Ba hSa using hfa
  have hC : ∀ (y : V → ℝ) (r : ℝ), f y ≤ (r : WithTop ℝ) ↔
      ∀ i, C i none * r + ∑ v, C i (some v) * y v ≤ B i := by
    intro y r
    have := Set.ext_iff.mp hS (fun o => Option.elim o r y)
    simpa [Fintype.sum_option] using this
  have hCa : ∀ a (t s : ℝ), fa a t ≤ (s : WithTop ℝ) ↔
      ∀ j, Ca a j false * t + Ca a j true * s ≤ Ba a j := by
    intro a t s
    have := Set.ext_iff.mp (hSa a) (fun b => cond b s t)
    simp only [Set.mem_setOf_eq, Fintype.sum_bool, cond_true, cond_false] at this
    rw [this]
    exact forall_congr' (fun j => by rw [add_comm])
  refine ⟨fun xi hfe => ⟨fun ho => hard_core tail head fa f m C B ma Ca Ba hC hCa xi ho,
    fun ⟨p, hp⟩ => easy_dir tail head fa f xi p hfe hp⟩,
    fun xi p ho hp xi' hf' => ⟨fun ho' => transfer_dir tail head fa f xi p ho hp xi' ho',
      fun hp' => easy_dir tail head fa f xi' p hf' hp'⟩⟩

end PC

end DiscreteConvex.NetworkFlowsB

open DiscreteConvex.NetworkFlowsB
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem solution (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (hf : IsPolyhedralConvex f) (hfa : ∀ a, IsPolyhedralConvexArc (fa a)) :
    (∀ xi, FeasibleFlowMCFP3 tail head fa f xi →
      (OptimalFlowMCFP3 tail head fa f xi ↔ ∃ p : V → ℝ, IsOptimalPotential tail head fa f xi p)) ∧
    (∀ xi p, OptimalFlowMCFP3 tail head fa f xi → IsOptimalPotential tail head fa f xi p →
      ∀ xi', FeasibleFlowMCFP3 tail head fa f xi' →
        (OptimalFlowMCFP3 tail head fa f xi' ↔ IsOptimalPotential tail head fa f xi' p)) := by
  exact potential_criterion_mcfp3_core tail head fa f hf hfa
