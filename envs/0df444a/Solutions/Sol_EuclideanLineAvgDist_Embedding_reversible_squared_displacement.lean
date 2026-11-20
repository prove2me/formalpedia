-- Prove2me | solution 1 for EuclideanLineAvgDist.Embedding.reversible_squared_displacement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:41:06.731493+00:00
-- url     : https://prove2.me/submissions/e75bda88-1a18-4fb4-a869-f8ebc6d68e83

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic
import Definitions.Def_EuclideanLineAvgDist_Embedding_Markov

section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Reversible

section Abstract

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Dirichlet-type form decreases under `T`. -/
lemma dirichlet_le (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (T : V →ₗ[ℝ] V)
    (hsym : ∀ u v, B u v = B v u) (hsa : ∀ u v, B (T u) v = B u (T v))
    (hc : ∀ u, B (T u) (T u) ≤ B u u) (hpos : ∀ u, 0 ≤ B u u) (h : V) :
    B (T h) (T h) - B (T (T h)) (T h) ≤ B h h - B (T h) h := by
  have h1 := hpos (T h - T (T h) + (h - T h))
  have h2 := hc (h - T h)
  have h3 := hpos (h - T h)
  have e1 : B (T (T h)) h = B (T h) (T h) := hsa (T h) h
  have e2 : B (T h) h = B h (T h) := hsym _ _
  have e3 : B (T (T h)) (T h) = B (T h) (T (T h)) := hsym _ _
  have e4 := hsym (T (T h)) h
  have e5 := hsym (T (T h)) (T h)
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply] at h1 h2 h3
  nlinarith [hsym h (T h), hsym (T h) (T (T h)), hsym h (T (T h)), hsym (T h) h]

lemma iter_selfadj (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (T : V →ₗ[ℝ] V)
    (hsa : ∀ u v, B (T u) v = B u (T v)) (a : ℕ) (u v : V) :
    B (T^[a] u) v = B u (T^[a] v) := by
  induction a generalizing u with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply, ih, hsa, Function.iterate_succ_apply']

lemma iter_pair (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (T : V →ₗ[ℝ] V)
    (hsym : ∀ u v, B u v = B v u) (hsa : ∀ u v, B (T u) v = B u (T v)) (a b : ℕ) (f : V) :
    B (T^[a + b] f) f = B (T^[a] f) (T^[b] f) := by
  rw [Function.iterate_add_apply, iter_selfadj B T hsa, hsym]

lemma dirichlet_iter (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (T : V →ₗ[ℝ] V)
    (hsym : ∀ u v, B u v = B v u) (hsa : ∀ u v, B (T u) v = B u (T v))
    (hc : ∀ u, B (T u) (T u) ≤ B u u) (hpos : ∀ u, 0 ≤ B u u) (f : V) (m : ℕ) :
    B (T^[m] f) (T^[m] f) - B (T (T^[m] f)) (T^[m] f) ≤ B f f - B (T f) f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (dirichlet_le B T hsym hsa hc hpos _).trans ih

lemma step_le (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (T : V →ₗ[ℝ] V)
    (hsym : ∀ u v, B u v = B v u) (hsa : ∀ u v, B (T u) v = B u (T v))
    (hc : ∀ u, B (T u) (T u) ≤ B u u) (hpos : ∀ u, 0 ≤ B u u) (f : V) (j : ℕ) :
    B (T^[j] f) f - B (T^[j + 1] f) f ≤ B f f - B (T f) f := by
  have hd := dirichlet_iter B T hsym hsa hc hpos f
  have hT : ∀ m, T^[m + 1] f = T (T^[m] f) := fun m => Function.iterate_succ_apply' T m f
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · have h1 : B (T^[2 * m] f) f = B (T^[m] f) (T^[m] f) := by
      rw [two_mul, iter_pair B T hsym hsa]
    have h2 : B (T^[2 * m + 1] f) f = B (T (T^[m] f)) (T^[m] f) := by
      rw [show 2 * m + 1 = (m + 1) + m by ring, iter_pair B T hsym hsa, hT]
    rw [h1, h2]
    exact hd m
  · have h1 : B (T^[2 * m + 1] f) f = B (T (T^[m] f)) (T^[m] f) := by
      rw [show 2 * m + 1 = (m + 1) + m by ring, iter_pair B T hsym hsa, hT]
    have h2 : B (T^[2 * m + 1 + 1] f) f = B (T (T^[m] f)) (T (T^[m] f)) := by
      rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) by ring, iter_pair B T hsym hsa, hT]
    rw [h1, h2]
    have := hpos (T^[m] f - T (T^[m] f))
    simp only [map_sub, LinearMap.sub_apply] at this
    have := hd m
    nlinarith [hsym (T^[m] f) (T (T^[m] f)), hpos (T^[m] f - T (T^[m] f)), map_sub (B (T^[m] f - T (T^[m] f))) (T^[m] f) (T (T^[m] f))]

lemma main_abstract (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (T : V →ₗ[ℝ] V)
    (hsym : ∀ u v, B u v = B v u) (hsa : ∀ u v, B (T u) v = B u (T v))
    (hc : ∀ u, B (T u) (T u) ≤ B u u) (hpos : ∀ u, 0 ≤ B u u) (f : V) (i : ℕ) :
    B f f - B (T^[i] f) f ≤ i * (B f f - B (T f) f) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := step_le B T hsym hsa hc hpos f i
    push_cast
    linarith

end Abstract

section Markov

open EuclideanLineAvgDist.Embedding

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Bounded measurable real functions. -/
def Good (f : Ω → ℝ) : Prop := Measurable f ∧ ∃ C : ℝ, ∀ x, |f x| ≤ C

lemma Good.integrable {f : Ω → ℝ} (hf : Good f) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Integrable f μ := by
  obtain ⟨hm, C, hC⟩ := hf
  exact Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa using hC x)

lemma Good.zero : Good (0 : Ω → ℝ) := ⟨measurable_const, 0, fun x => by simp⟩

lemma Good.add {f g : Ω → ℝ} (hf : Good f) (hg : Good g) : Good (f + g) := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hg
  refine ⟨hm.add hm', C + C', fun x => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hC x) (hC' x))

lemma Good.smul {f : Ω → ℝ} (c : ℝ) (hf : Good f) : Good (c • f) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm.const_smul c, |c| * C, fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)

lemma Good.mul {f g : Ω → ℝ} (hf : Good f) (hg : Good g) : Good (f * g) := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hg
  refine ⟨hm.mul hm', C * C', fun x => ?_⟩
  simp only [Pi.mul_apply, abs_mul]
  exact mul_le_mul (hC x) (hC' x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))

/-- The Markov operator `f ↦ ∫ f(y) P(x,dy)`. -/
noncomputable def Tf (P : Kernel Ω Ω) (f : Ω → ℝ) : Ω → ℝ := fun x => ∫ y, f y ∂(P x)

lemma Good.tfOp (P : Kernel Ω Ω) [IsMarkovKernel P] {f : Ω → ℝ} (hf : Good f) : Good (Tf P f) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm.stronglyMeasurable.integral_kernel.measurable, C, fun x => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := P x) (f := f) (C := C)
    (Filter.Eventually.of_forall fun y => by simpa using hC y)
  show |∫ y, f y ∂(P x)| ≤ C
  simpa using this

instance kernelIter_markov (P : Kernel Ω Ω) [IsMarkovKernel P] (i : ℕ) :
    IsMarkovKernel (kernelIter P i) := by
  induction i with
  | zero => unfold kernelIter; infer_instance
  | succ i ih =>
    unfold kernelIter
    have := ih
    infer_instance

lemma Good.tfIter (P : Kernel Ω Ω) [IsMarkovKernel P] {f : Ω → ℝ} (hf : Good f) (i : ℕ) :
    Good ((Tf P)^[i] f) := by
  induction i with
  | zero => exact hf
  | succ i ih => rw [Function.iterate_succ_apply']; exact ih.tfOp P

lemma integral_iter (P : Kernel Ω Ω) [IsMarkovKernel P] (i : ℕ) :
    ∀ (f : Ω → ℝ), Good f → ∀ x, ∫ y, f y ∂(kernelIter P i x) = (Tf P)^[i] f x := by
  induction i with
  | zero =>
    intro f hf x
    simp only [kernelIter, Kernel.id_apply, Function.iterate_zero, id]
    exact integral_dirac' _ _ hf.1.stronglyMeasurable
  | succ i ih =>
    intro f hf x
    have h1 : kernelIter P (i + 1) = P ∘ₖ kernelIter P i := rfl
    rw [h1, Kernel.integral_comp (hf.integrable _)]
    rw [Function.iterate_succ_apply]
    exact ih (Tf P f) (hf.tfOp P) x

variable (P : Kernel Ω Ω) [IsMarkovKernel P] (π : Measure Ω) [IsProbabilityMeasure π]

lemma integral_Tf (hrev : IsReversible π P) {h : Ω → ℝ} (hh : Good h) :
    ∫ x, Tf P h x ∂π = ∫ x, h x ∂π := by
  have hg : Good (fun p : Ω × Ω => h p.2) := ⟨hh.1.comp measurable_snd, hh.2.choose, fun p => hh.2.choose_spec _⟩
  have hg1 : Good (fun p : Ω × Ω => h p.1) := ⟨hh.1.comp measurable_fst, hh.2.choose, fun p => hh.2.choose_spec _⟩
  have e1 : ∫ x, Tf P h x ∂π = ∫ p, h p.2 ∂(π ⊗ₘ P) := by
    rw [Measure.integral_compProd (hg.integrable _)]
    rfl
  have e2 : ∫ p, h p.2 ∂(π ⊗ₘ P) = ∫ p, h p.1 ∂(π ⊗ₘ P) := by
    conv_lhs => rw [← hrev]
    rw [integral_map measurable_swap.aemeasurable hg.1.aestronglyMeasurable]
    rfl
  rw [e1, e2, Measure.integral_compProd (hg1.integrable _)]
  simp

lemma integral_Tf_iter (hrev : IsReversible π P) (i : ℕ) :
    ∀ {h : Ω → ℝ}, Good h → ∫ x, (Tf P)^[i] h x ∂π = ∫ x, h x ∂π := by
  induction i with
  | zero => intro h _; rfl
  | succ i ih =>
    intro h hh
    rw [Function.iterate_succ_apply]
    rw [ih (hh.tfOp P), integral_Tf P π hrev hh]

lemma selfadj (hrev : IsReversible π P) {u v : Ω → ℝ} (hu : Good u) (hv : Good v) :
    ∫ x, Tf P u x * v x ∂π = ∫ x, u x * Tf P v x ∂π := by
  obtain ⟨hmu, Cu, hCu⟩ := hu
  obtain ⟨hmv, Cv, hCv⟩ := hv
  have hu' : Good u := ⟨hmu, Cu, hCu⟩
  have hv' : Good v := ⟨hmv, Cv, hCv⟩
  have hF : Good (fun p : Ω × Ω => u p.1 * v p.2) :=
    (Good.mul ⟨hmu.comp measurable_fst, Cu, fun p => hCu _⟩ ⟨hmv.comp measurable_snd, Cv, fun p => hCv _⟩)
  have hF' : Good (fun p : Ω × Ω => v p.1 * u p.2) :=
    (Good.mul ⟨hmv.comp measurable_fst, Cv, fun p => hCv _⟩ ⟨hmu.comp measurable_snd, Cu, fun p => hCu _⟩)
  have e1 : ∫ x, Tf P u x * v x ∂π = ∫ p, v p.1 * u p.2 ∂(π ⊗ₘ P) := by
    rw [Measure.integral_compProd (hF'.integrable _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Tf]
    rw [integral_const_mul, mul_comm]
  have e2 : ∫ x, u x * Tf P v x ∂π = ∫ p, u p.1 * v p.2 ∂(π ⊗ₘ P) := by
    rw [Measure.integral_compProd (hF.integrable _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Tf]
    rw [integral_const_mul]
  rw [e1, e2]
  conv_rhs => rw [← hrev]
  rw [integral_map measurable_swap.aemeasurable hF.1.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp [mul_comm]

lemma sq_integral_le (μ : Measure Ω) [IsProbabilityMeasure μ] {u : Ω → ℝ} (hu : Good u) :
    (∫ y, u y ∂μ) ^ 2 ≤ ∫ y, u y ^ 2 ∂μ := by
  have hu2 : Good (fun y => u y ^ 2) := by
    have := hu.mul hu
    convert this using 1
    ext y; simp [pow_two]
  set m := ∫ y, u y ∂μ with hm
  have int1 := hu.integrable μ
  have int2 := hu2.integrable μ
  have e : ∫ y, (u y - m) ^ 2 ∂μ = ∫ y, u y ^ 2 ∂μ - m ^ 2 := by
    have e : (fun y => (u y - m) ^ 2) = fun y => (u y ^ 2 - (2 * m) * u y) + m ^ 2 := by
      ext y; ring
    have h3 : Integrable (fun y => u y ^ 2 - 2 * m * u y) μ := int2.sub (int1.const_mul _)
    rw [e, integral_add h3 (integrable_const _),
      integral_sub int2 (int1.const_mul _), integral_const_mul, integral_const]
    simp [← hm]
    ring
  have : 0 ≤ ∫ y, (u y - m) ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg _
  linarith

/-- Submodule of bounded measurable functions. -/
def Wsp (Ω : Type*) [MeasurableSpace Ω] : Submodule ℝ (Ω → ℝ) where
  carrier := {f | Good f}
  add_mem' := fun ha hb => Good.add ha hb
  zero_mem' := Good.zero
  smul_mem' := fun c _ h => Good.smul c h

/-- `Tf` as a linear map on bounded measurable functions. -/
noncomputable def Tl : Wsp Ω →ₗ[ℝ] Wsp Ω where
  toFun f := ⟨Tf P f.1, f.2.tfOp P⟩
  map_add' f g := by
    ext x
    exact integral_add (f.2.integrable _) (g.2.integrable _)
  map_smul' c f := by
    ext x
    exact integral_smul c _

/-- The `L²(π)` bilinear form. -/
noncomputable def Bf : Wsp Ω →ₗ[ℝ] Wsp Ω →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∫ x, u.1 x * v.1 x ∂π)
    (fun u1 u2 v => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact integral_add ((u1.2.mul v.2).integrable π) ((u2.2.mul v.2).integrable π))
    (fun c u v => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun u v1 v2 => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add ((u.2.mul v1.2).integrable π) ((u.2.mul v2.2).integrable π))
    (fun c u v => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1; ext x; ring)

lemma Tl_iter_coe (f : Wsp Ω) (i : ℕ) : ((Tl P)^[i] f).1 = (Tf P)^[i] f.1 := by
  induction i generalizing f with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

lemma real_ineq (hrev : IsReversible π P) {f : Ω → ℝ} (hf : Good f) (i : ℕ) :
    ∫ x, f x * f x ∂π - ∫ x, (Tf P)^[i] f x * f x ∂π ≤
      i * (∫ x, f x * f x ∂π - ∫ x, Tf P f x * f x ∂π) := by
  have := main_abstract (Bf π) (Tl P)
    (fun u v => by
      show ∫ x, u.1 x * v.1 x ∂π = ∫ x, v.1 x * u.1 x ∂π
      simp_rw [mul_comm])
    (fun u v => selfadj P π hrev u.2 v.2)
    (fun u => by
      show ∫ x, Tf P u.1 x * Tf P u.1 x ∂π ≤ ∫ x, u.1 x * u.1 x ∂π
      have h1 := integral_Tf P π hrev (h := fun y => u.1 y * u.1 y) (u.2.mul u.2)
      rw [← h1]
      refine integral_mono (((u.2.tfOp P).mul (u.2.tfOp P)).integrable π)
        (((u.2.mul u.2).tfOp P).integrable π) fun x => ?_
      have := sq_integral_le (P x) u.2
      simp only [Tf, pow_two] at this ⊢
      exact this)
    (fun u => integral_nonneg fun x => mul_self_nonneg _) ⟨f, hf⟩ i
  have e := Tl_iter_coe P ⟨f, hf⟩ i
  have e1 : ((Tl P) ⟨f, hf⟩).1 = Tf P f := rfl
  simpa [Bf, e, e1] using this

lemma Good.sub {f g : Ω → ℝ} (hf : Good f) (hg : Good g) : Good (f - g) := by
  have := hf.add (hg.smul (-1))
  convert this using 1
  ext x; simp [sub_eq_add_neg]

lemma Good.fst {f : Ω → ℝ} (hf : Good f) : Good (fun p : Ω × Ω => f p.1) :=
  ⟨hf.1.comp measurable_fst, hf.2.choose, fun p => hf.2.choose_spec _⟩

lemma Good.snd {f : Ω → ℝ} (hf : Good f) : Good (fun p : Ω × Ω => f p.2) :=
  ⟨hf.1.comp measurable_snd, hf.2.choose, fun p => hf.2.choose_spec _⟩

lemma Good.mul_self {f : Ω → ℝ} (hf : Good f) : Good (fun x => f x * f x) := hf.mul hf

lemma real_identity (hrev : IsReversible π P) {f : Ω → ℝ} (hf : Good f) (i : ℕ) :
    ∫ p, (f p.2 - f p.1) ^ 2 ∂(π ⊗ₘ kernelIter P i) =
      2 * (∫ x, f x * f x ∂π - ∫ x, (Tf P)^[i] f x * f x ∂π) := by
  have hG : Good (fun p : Ω × Ω => (f p.2 - f p.1) ^ 2) := by
    have := (hf.snd.sub hf.fst).mul (hf.snd.sub hf.fst)
    convert this using 1
    ext p; simp [pow_two]
  rw [Measure.integral_compProd (hG.integrable _)]
  have hff := hf.mul_self
  have inner : ∀ x, ∫ y, (f y - f x) ^ 2 ∂(kernelIter P i x) =
      (Tf P)^[i] (fun y => f y * f y) x - 2 * f x * (Tf P)^[i] f x + f x * f x := by
    intro x
    have e : (fun y => (f y - f x) ^ 2) = fun y => (f y * f y - (2 * f x) * f y) + f x * f x := by
      ext y; ring
    have int1 := hf.integrable (kernelIter P i x)
    have int2 := hff.integrable (kernelIter P i x)
    have h3 : Integrable (fun y => f y * f y - (2 * f x) * f y) (kernelIter P i x) :=
      int2.sub (int1.const_mul _)
    rw [e, integral_add h3 (integrable_const _), integral_sub int2 (int1.const_mul _),
      integral_const_mul, integral_const, integral_iter P i _ hff x, integral_iter P i _ hf x]
    simp
  simp_rw [inner]
  have hA := hff.tfIter P i
  have hB := hf.tfIter P i
  have iA := hA.integrable π
  have iB : Integrable (fun x => f x * (Tf P)^[i] f x) π := (hf.mul hB).integrable π
  have iC := hff.integrable π
  have e2 : ∀ x, 2 * f x * (Tf P)^[i] f x = 2 * (f x * (Tf P)^[i] f x) := fun x => by ring
  simp_rw [e2]
  have iD : Integrable (fun x => (Tf P)^[i] (fun y => f y * f y) x - 2 * (f x * (Tf P)^[i] f x)) π :=
    iA.sub (iB.const_mul 2)
  rw [integral_add iD iC, integral_sub iA (iB.const_mul 2),
    integral_const_mul, integral_Tf_iter P π hrev i hff]
  have : ∫ x, f x * (Tf P)^[i] f x ∂π = ∫ x, (Tf P)^[i] f x * f x ∂π := by
    simp_rw [mul_comm]
  rw [this]
  ring

omit [IsMarkovKernel P] in
lemma kernelIter_one : kernelIter P 1 = P := by
  show P ∘ₖ Kernel.id = P
  exact Kernel.comp_id P

lemma scalar_bounded (hrev : IsReversible π P) {f : Ω → ℝ} (hf : Good f) (i : ℕ) :
    ∫⁻ p, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) ∂(π ⊗ₘ kernelIter P i) ≤
      (i : ℝ≥0∞) * ∫⁻ p, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) ∂(π ⊗ₘ P) := by
  have hG : Good (fun p : Ω × Ω => (f p.2 - f p.1) ^ 2) := by
    have := (hf.snd.sub hf.fst).mul (hf.snd.sub hf.fst)
    convert this using 1
    ext p; simp [pow_two]
  have br : ∀ (μ : Measure (Ω × Ω)) [IsFiniteMeasure μ],
      ∫⁻ p, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) ∂μ = ENNReal.ofReal (∫ p, (f p.2 - f p.1) ^ 2 ∂μ) := by
    intro μ _
    rw [ofReal_integral_eq_lintegral_ofReal (hG.integrable μ)
      (Filter.Eventually.of_forall fun p => sq_nonneg _)]
  have h1 := real_identity P π hrev hf 1
  rw [kernelIter_one] at h1
  rw [br, br, h1, real_identity P π hrev hf i, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have := real_ineq P π hrev hf i
  have h4 : ((Tf P)^[1] f) = Tf P f := rfl
  rw [h4] at *
  nlinarith

/-- Clamping to `[-n, n]`. -/
def clampN (n : ℝ) (x : ℝ) : ℝ := max (-n) (min n x)

lemma clampN_lip (n : ℝ) (a b : ℝ) : (clampN n a - clampN n b) ^ 2 ≤ (a - b) ^ 2 := by
  have hL : LipschitzWith 1 (clampN n) := (LipschitzWith.id.const_min n).const_max (-n)
  have := hL.dist_le_mul a b
  rw [Real.dist_eq, Real.dist_eq] at this
  simp only [NNReal.coe_one, one_mul] at this
  exact sq_le_sq.2 (by simpa using this)

lemma clampN_eq (n a : ℝ) (h : |a| ≤ n) : clampN n a = a := by
  have := abs_le.1 h
  unfold clampN
  rw [min_eq_right this.2, max_eq_right this.1]

lemma Good.clamp {f : Ω → ℝ} (hf : Measurable f) (n : ℝ) : Good (fun x => clampN n (f x)) := by
  refine ⟨measurable_const.max (measurable_const.min hf), |n|, fun x => ?_⟩
  show |clampN n (f x)| ≤ |n|
  unfold clampN
  rw [abs_le]
  constructor
  · exact (neg_le_neg (le_abs_self n)).trans (le_max_left _ _)
  · refine max_le ?_ ?_
    · linarith [neg_abs_le n, abs_nonneg n]
    · exact (min_le_left _ _).trans (le_abs_self n)

lemma scalar_general (hrev : IsReversible π P) {f : Ω → ℝ} (hf : Measurable f) (i : ℕ) :
    ∫⁻ p, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) ∂(π ⊗ₘ kernelIter P i) ≤
      (i : ℝ≥0∞) * ∫⁻ p, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) ∂(π ⊗ₘ P) := by
  set F : ℕ → Ω × Ω → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal ((clampN n (f p.2) - clampN n (f p.1)) ^ 2) with hF
  have hFm : ∀ n, Measurable (F n) := fun n => by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (((Good.clamp hf n).1.comp measurable_snd).sub
      ((Good.clamp hf n).1.comp measurable_fst)).pow_const 2
  have hlim : ∀ p : Ω × Ω, Filter.liminf (fun n => F n p) Filter.atTop =
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) := by
    intro p
    refine Filter.Tendsto.liminf_eq ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (⌈max |f p.2| |f p.1|⌉₊)] with n hn
    have h0 : max |f p.2| |f p.1| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    simp only [hF]
    rw [clampN_eq _ _ ((le_max_left _ _).trans h0), clampN_eq _ _ ((le_max_right _ _).trans h0)]
  have hn : ∀ n : ℕ, ∫⁻ p, F n p ∂(π ⊗ₘ kernelIter P i) ≤
      (i : ℝ≥0∞) * ∫⁻ p, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) ∂(π ⊗ₘ P) := by
    intro n
    refine (scalar_bounded P π hrev (Good.clamp hf n) i).trans ?_
    refine mul_le_mul' le_rfl (lintegral_mono fun p => ?_)
    exact ENNReal.ofReal_le_ofReal (clampN_lip _ _ _)
  calc ∫⁻ p, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) ∂(π ⊗ₘ kernelIter P i)
      = ∫⁻ p, Filter.liminf (fun n => F n p) Filter.atTop ∂(π ⊗ₘ kernelIter P i) := by
        simp_rw [hlim]
    _ ≤ Filter.liminf (fun n => ∫⁻ p, F n p ∂(π ⊗ₘ kernelIter P i)) Filter.atTop :=
        lintegral_liminf_le hFm
    _ ≤ Filter.liminf (fun _ : ℕ => (i : ℝ≥0∞) *
          ∫⁻ p, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) ∂(π ⊗ₘ P)) Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hn)
    _ = _ := Filter.liminf_const _

lemma sqDisp_eq {k : ℕ} (φ : Ω → Eucl k) (hφ : Measurable φ) (μ : Measure (Ω × Ω)) :
    sqDisplacement φ μ =
      ∑ c : Fin k, ∫⁻ p, ENNReal.ofReal ((φ p.2 c - φ p.1 c) ^ 2) ∂μ := by
  have hc : ∀ c : Fin k, Measurable fun x => φ x c := fun c =>
    (EuclideanSpace.proj c).continuous.measurable.comp hφ
  unfold sqDisplacement
  rw [← lintegral_finset_sum]
  · refine lintegral_congr fun p => ?_
    rw [EuclideanSpace.norm_sq_eq, ← ENNReal.ofReal_sum_of_nonneg (fun c _ => sq_nonneg _)]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  · intro c _
    exact ENNReal.measurable_ofReal.comp
      ((((hc c).comp measurable_snd).sub ((hc c).comp measurable_fst)).pow_const 2)

end Markov

end EuclideanLineAvgDist.Dev.Reversible

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace EuclideanLineAvgDist

open EuclideanLineAvgDist.Embedding in
theorem chk_reversible_squared_displacement {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (φ : Ω → Eucl k) (hφ : Measurable φ)
    (P : Kernel Ω Ω) [IsMarkovKernel P] (π : Measure Ω) [IsProbabilityMeasure π]
    (hrev : IsReversible π P) (i : ℕ) (hi : 1 ≤ i) :
    sqDisplacement φ (π ⊗ₘ kernelIter P i) ≤ (i : ℝ≥0∞) * sqDisplacement φ (π ⊗ₘ P) := by
  have hc : ∀ c : Fin k, Measurable fun x => φ x c := fun c =>
    (EuclideanSpace.proj c).continuous.measurable.comp hφ
  rw [Dev.Reversible.sqDisp_eq φ hφ, Dev.Reversible.sqDisp_eq φ hφ, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => Dev.Reversible.scalar_general P π hrev (hc c) i

end EuclideanLineAvgDist

end

theorem solution : type_of% @EuclideanLineAvgDist.chk_reversible_squared_displacement := @EuclideanLineAvgDist.chk_reversible_squared_displacement
