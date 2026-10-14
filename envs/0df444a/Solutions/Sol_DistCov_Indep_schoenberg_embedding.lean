-- Prove2me | solution 1 for DistCov.Indep.schoenberg_embedding
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T21:48:42.317183+00:00
-- url     : https://prove2.me/submissions/a4fde5b0-af14-448b-89df-3325b07f3285

import Definitions.Def_DistCov_Indep_Setting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Topology InnerProductSpace
open DistCov.Indep
namespace DistCovSchoenberg

lemma negType_of_embedding {X H : Type*} [MetricSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ) : NegType X := by
  intro n x α hα
  have he := inner_sum_smul_sum_smul_of_sum_eq_zero
    (fun i => ϕ (x i)) hα (fun i => ϕ (x i)) hα
  have hd (i j : Fin n) := hϕ (x i) (x j)
  simp_rw [← sq, ← hd] at he
  have hp : 0 ≤ inner ℝ (∑ i, α i • ϕ (x i)) (∑ i, α i • ϕ (x i)) := real_inner_self_nonneg
  linarith

def kernel {X : Type*} [MetricSpace X] (o x y : X) : ℝ :=
  (dist x o + dist y o - dist x y) / 2

lemma kernel_symm {X : Type*} [MetricSpace X] (o x y : X) :
    kernel o x y = kernel o y x := by
  unfold kernel
  rw [dist_comm y x]
  ring

lemma kernel_diag {X : Type*} [MetricSpace X] (o x : X) :
    kernel o x x = dist x o := by simp [kernel]

lemma kernel_distance {X : Type*} [MetricSpace X] (o x y : X) :
    kernel o x x - 2 * kernel o x y + kernel o y y = dist x y := by
  rw [kernel_diag, kernel_diag]
  unfold kernel
  ring

lemma kernel_nonneg {X : Type*} [MetricSpace X] (hn : NegType X)
    (o : X) {n : ℕ} (x : Fin n → X) (α : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, α i * α j * kernel o (x i) (x j) := by
  classical
  let a := ∑ i, α i
  let y : Fin (n+1) → X := Fin.cons o x
  let β : Fin (n+1) → ℝ := Fin.cons (-a) α
  have hb : ∑ i, β i = 0 := by simp [β, Fin.sum_univ_succ, a]
  have h := hn (n+1) y β hb
  have he : (∑ i, ∑ j, β i * β j * dist (y i) (y j)) =
      (∑ i, ∑ j, α i * α j * dist (x i) (x j)) -
        2 * a * (∑ i, α i * dist (x i) o) := by
    simp only [Fin.sum_univ_succ, y, β, Fin.cons_zero, Fin.cons_succ, dist_self,
      mul_zero, Finset.sum_add_distrib, zero_add]
    simp only [dist_comm o, neg_mul, mul_neg, Finset.sum_neg_distrib]
    have ht (i : Fin n) : α i * a * dist (x i) o = a * (α i * dist (x i) o) := by ring
    have hu (i : Fin n) : a * α i * dist (x i) o = a * (α i * dist (x i) o) := by ring
    rw [show (∑ i, α i * a * dist (x i) o) = a * ∑ i, α i * dist (x i) o by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => ht i)]
    rw [show (∑ i, a * α i * dist (x i) o) = a * ∑ i, α i * dist (x i) o by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => hu i)]
    ring
  rw [he] at h
  have hk : (∑ i, ∑ j, α i * α j * kernel o (x i) (x j)) =
      a * (∑ i, α i * dist (x i) o) -
        (∑ i, ∑ j, α i * α j * dist (x i) (x j)) / 2 := by
    have ht (i j : Fin n) : α i * α j * kernel o (x i) (x j) =
        ((α i * dist (x i) o) * α j + α i * (α j * dist (x j) o) -
          α i * α j * dist (x i) (x j)) / 2 := by unfold kernel; ring
    calc
      _ = (∑ i, ∑ j, ((α i * dist (x i) o) * α j +
          α i * (α j * dist (x j) o) - α i * α j * dist (x i) (x j))) / 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun j _ => ht i j)
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul]
        dsimp [a]
        ring
  rw [hk]
  linarith


def form {X : Type*} [MetricSpace X] (o : X) :
    (X →₀ ℝ) →ₗ[ℝ] (X →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun x => Finsupp.linearCombination ℝ (kernel o x))

lemma form_sum {X : Type*} [MetricSpace X] (o : X) (f g : X →₀ ℝ) :
    form o f g = ∑ x ∈ f.support, ∑ y ∈ g.support,
      f x * g y * kernel o x y := by
  classical
  simp [form, Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum, mul_assoc]

lemma form_symm {X : Type*} [MetricSpace X] (o : X) (f g : X →₀ ℝ) :
    form o f g = form o g f := by
  classical
  rw [form_sum, form_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [kernel_symm o y x]
  ring

lemma form_nonneg {X : Type*} [MetricSpace X] (hn : NegType X) (o : X)
    (f : X →₀ ℝ) : 0 ≤ form o f f := by
  classical
  let e := f.support.equivFin.symm
  have h := kernel_nonneg hn o (fun i => (e i).1) (fun i => f (e i).1)
  rw [form_sum]
  have hs (F : X → ℝ) : (∑ i, F (e i).1) = ∑ x ∈ f.support, F x := by
    exact (e.sum_comp (fun x : f.support => F x)).trans (by
      simpa only [Finset.attach_eq_univ] using Finset.sum_attach f.support F)
  rw [show (∑ i, ∑ j, f (e i).1 * f (e j).1 * kernel o (e i).1 (e j).1) =
      ∑ x ∈ f.support, ∑ y ∈ f.support, f x * f y * kernel o x y by
    calc
      _ = ∑ i, ∑ y ∈ f.support, f (e i).1 * f y * kernel o (e i).1 y := by
        exact Finset.sum_congr rfl (fun i _ => hs (fun y => f (e i).1 * f y * kernel o (e i).1 y))
      _ = _ := hs (fun x => ∑ y ∈ f.support, f x * f y * kernel o x y)] at h
  exact h


@[instance_reducible]
def core {X : Type*} [MetricSpace X] (hn : NegType X) (o : X) :
    PreInnerProductSpace.Core ℝ (X →₀ ℝ) where
  inner := fun f g => form o f g
  conj_inner_symm f g := by simpa using form_symm o g f
  re_inner_nonneg := form_nonneg hn o
  add_left f g h := by simp only [map_add, LinearMap.add_apply]
  smul_left f g r := by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RCLike.conj_to_real]

lemma embedding_continuous {X H : Type*} [MetricSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ) : Continuous ϕ := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨ε^2, sq_pos_of_pos hε, ?_⟩
  intro y hy
  rw [dist_eq_norm]
  have hd := hϕ y x
  have hp := norm_nonneg (ϕ y - ϕ x)
  nlinarith

lemma basis_countable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [SecondCountableTopology H] (w : Set H) (b : HilbertBasis w ℝ H)
    (hb : (b : w → H) = Subtype.val) : w.Countable := by
  have hd : IsDiscrete w := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x hx
    refine ⟨Metric.ball x 1, Metric.isOpen_ball, ?_⟩
    ext y
    constructor
    · rintro ⟨hy,hyw⟩
      change y = x
      by_contra hne
      have hi : (⟨x,hx⟩ : w) ≠ ⟨y,hyw⟩ := fun he => hne (congrArg Subtype.val he).symm
      have hn := norm_sub_sq_real (b ⟨x,hx⟩) (b ⟨y,hyw⟩)
      rw [b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one, b.orthonormal.inner_eq_zero hi] at hn
      simp only [dist_eq_norm, Metric.mem_ball] at hy
      rw [hb] at hn
      have hp : 0 ≤ ‖x-y‖ := norm_nonneg _
      have hl : ‖x-y‖ < 1 := by simpa [norm_sub_rev] using hy
      nlinarith
    · intro hy
      have hxy : y = x := hy
      subst y
      exact ⟨by simp, hx⟩
  exact (HereditarilyLindelofSpace.isLindelof w).countable_of_isDiscrete hd

def coordIsometry (n : ℕ) : ℝ →ₗᵢ[ℝ] L2N :=
  (lp.lsingle (E := fun _ : ℕ => ℝ) 2 n).toLinearIsometry (by exact lp.isometry_single (E := fun _ : ℕ => ℝ) (p := 2) n)

lemma coords_orthogonal {ι : Type*} (k : ι ↪ ℕ) :
    OrthogonalFamily ℝ (fun _ : ι => ℝ) (fun i => coordIsometry (k i)) := by
  intro i j hij a b
  change inner ℝ (lp.single 2 (k i) a : L2N) (lp.single 2 (k j) b : L2N) = 0
  rw [lp.inner_single_left, lp.coeFn_single, Pi.single_eq_of_ne (fun he => hij (k.injective he))]
  simp

lemma exists_l2_embedding (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H] : Nonempty (H →ₗᵢ[ℝ] L2N) := by
  classical
  obtain ⟨w,b,hb⟩ := exists_hilbertBasis ℝ H
  letI : Countable w := (basis_countable w b hb).to_subtype
  letI := Encodable.ofCountable w
  let k : w ↪ ℕ := ⟨Encodable.encode, Encodable.encode_injective⟩
  exact ⟨(coords_orthogonal k).linearIsometry.comp b.repr.toLinearIsometry⟩

lemma embedding_of_negType {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    (hn : NegType X) : ∃ ϕ : X → L2N, IsNegTypeEmbedding ϕ := by
  classical
  by_cases hX : Nonempty X
  · obtain ⟨o⟩ := hX
    letI : PreInnerProductSpace.Core ℝ (X →₀ ℝ) := core hn o
    letI : SeminormedAddCommGroup (X →₀ ℝ) := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)
    letI : InnerProductSpace ℝ (X →₀ ℝ) := InnerProductSpace.ofCore (core hn o)
    let H := UniformSpace.Completion (SeparationQuotient (X →₀ ℝ))
    letI : NormedSpace ℝ H := inferInstance
    letI : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul
    let ϕ : X → H := fun x => ((SeparationQuotient.mk (Finsupp.single x (1 : ℝ)) : SeparationQuotient (X →₀ ℝ)) : H)
    have hi (x y : X) : inner ℝ (ϕ x) (ϕ y) = kernel o x y := by
      dsimp [ϕ]
      rw [UniformSpace.Completion.inner_coe, SeparationQuotient.inner_mk_mk]
      change form o (Finsupp.single x 1) (Finsupp.single y 1) = _
      simp [form]
    have hd : IsNegTypeEmbedding ϕ := by
      intro x y
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right]
      simp only [hi]
      rw [kernel_symm o y x]
      linarith [kernel_distance o x y]
    let C := (Submodule.span ℝ (Set.range ϕ)).topologicalClosure
    have hs : TopologicalSpace.IsSeparable (C : Set H) := by
      exact (TopologicalSpace.isSeparable_range (embedding_continuous ϕ hd)).span (R := ℝ) |>.closure
    letI : CompleteSpace C := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    letI : TopologicalSpace.SeparableSpace C := hs.separableSpace
    obtain ⟨f⟩ := exists_l2_embedding C
    let ψ : X → C := fun x => ⟨ϕ x, Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_range_self x))⟩
    refine ⟨fun x => f (ψ x), ?_⟩
    intro x y
    rw [← f.map_sub, f.norm_map]
    exact hd x y
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩

end DistCovSchoenberg

theorem solution {X : Type*} [MetricSpace X] [SecondCountableTopology X] :
    NegType X ↔ ∃ ϕ : X → L2N, IsNegTypeEmbedding ϕ := by
  constructor
  · exact DistCovSchoenberg.embedding_of_negType
  · rintro ⟨ϕ,hϕ⟩
    exact DistCovSchoenberg.negType_of_embedding ϕ hϕ

#print axioms solution
