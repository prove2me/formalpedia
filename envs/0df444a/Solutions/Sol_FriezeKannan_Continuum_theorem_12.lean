-- Prove2me | solution 1 for FriezeKannan.Continuum.theorem_12
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T23:12:23.995823+00:00
-- url     : https://prove2.me/submissions/1f43185f-db81-4a36-9c21-441288e99a90

-- Complete checked reconstruction of the native continuum cut-decomposition theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_FriezeKannan_Continuum_Setting
import Mathlib


-- Begin CutFamily

open MeasureTheory
open scoped BigOperators
namespace FriezeKannan.Continuum.Proof

structure CutFamily (n : ℕ) where
  left : Fin n → Set unitInterval
  right : Fin n → Set unitInterval
  coeff : Fin n → ℝ
  measurable : ∀ i, MeasurableSet (left i) ∧ MeasurableSet (right i)

noncomputable def CutFamily.residual {n : ℕ} (a : CutFamily n) (f : Sq → ℝ) : Sq → ℝ :=
  fun p => f p - cutFunSum a.left a.right a.coeff p

def CutFamily.empty : CutFamily 0 where
  left := Fin.elim0
  right := Fin.elim0
  coeff := Fin.elim0
  measurable := fun i => Fin.elim0 i

@[simp] theorem CutFamily.residual_empty (f : Sq → ℝ) : CutFamily.empty.residual f = f := by
  funext p
  simp [CutFamily.residual, cutFunSum]

noncomputable def CutFamily.append {n : ℕ} (a : CutFamily n)
    (S T : Set unitInterval) (d : ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    CutFamily (n+1) where
  left := Fin.snoc a.left S
  right := Fin.snoc a.right T
  coeff := Fin.snoc a.coeff d
  measurable := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using And.intro hS hT
    · simpa using a.measurable j

theorem CutFamily.residual_append {n : ℕ} (a : CutFamily n)
    (f : Sq → ℝ) (S T : Set unitInterval) (d : ℝ)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (a.append S T d hS hT).residual f = fun p => a.residual f p - cutFun S T d p := by
  funext p
  simp [CutFamily.residual, CutFamily.append, cutFunSum, Fin.sum_univ_castSucc, sub_add_eq_sub_sub]

end FriezeKannan.Continuum.Proof
-- End CutFamily

-- Begin RectangleBasic

open MeasureTheory

namespace FriezeKannan.Continuum.Proof

lemma norm_sq_nonneg (f : Sq → ℝ) : 0 ≤ ∫ p, f p ^ 2 :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma l2Norm_nonneg (f : Sq → ℝ) : 0 ≤ l2Norm f := Real.sqrt_nonneg _

lemma l2Norm_sq_eq_integral (f : Sq → ℝ) :
    l2Norm f ^ 2 = ∫ p, f p ^ 2 :=
  Real.sq_sqrt (norm_sq_nonneg f)

lemma cutFun_memLp (S T : Set unitInterval) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (d : ℝ) : MemLp (cutFun S T d) 2 := by
  exact (memLp_const d).indicator (hS.prod hT)

lemma residual_memLp {f : Sq → ℝ} (hf : MemLp f 2)
    (S T : Set unitInterval) (hS : MeasurableSet S) (hT : MeasurableSet T) (d : ℝ) :
    MemLp (fun p => f p - cutFun S T d p) 2 :=
  hf.sub (cutFun_memLp S T hS hT d)

lemma rect_measure_nonneg (S T : Set unitInterval) :
    0 ≤ volume.real (S ×ˢ T : Set Sq) := ENNReal.toReal_nonneg

lemma rect_measure_le_one (S T : Set unitInterval) :
    volume.real (S ×ˢ T : Set Sq) ≤ 1 := by
  exact measureReal_le_one

lemma rectInt_zero_of_measure_zero {f : Sq → ℝ} (S T : Set unitInterval)
    (h : volume.real (S ×ˢ T : Set Sq) = 0) : rectInt f S T = 0 := by
  have h' : volume (S ×ˢ T : Set Sq) = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (measure_ne_top _ _)
  simp [rectInt, h']

lemma norm_zero_rectInt {f : Sq → ℝ} (hf : MemLp f 2) (h : l2Norm f = 0)
    (S T : Set unitInterval) : rectInt f S T = 0 := by
  have hi : (∫ p, f p ^ 2) = 0 := by rw [← l2Norm_sq_eq_integral, h]; norm_num
  have hz : (fun p => f p ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      hf.integrable_sq).mp hi
  have hfz : f =ᵐ[volume] 0 := hz.mono fun p hp => by simpa using hp
  unfold rectInt
  rw [integral_congr_ae (ae_restrict_of_ae hfz)]
  simp

end FriezeKannan.Continuum.Proof
-- End RectangleBasic

-- Begin FamilyAnalytic

open MeasureTheory
open scoped BigOperators
namespace FriezeKannan.Continuum.Proof

theorem CutFamily.memLp_residual {n : ℕ} (a : CutFamily n)
    {f : Sq → ℝ} (hf : MemLp f 2) : MemLp (a.residual f) 2 := by
  apply hf.sub
  apply memLp_finsetSum
  intro i _
  exact cutFun_memLp (a.left i) (a.right i) (a.measurable i).1 (a.measurable i).2 (a.coeff i)

end FriezeKannan.Continuum.Proof
-- End FamilyAnalytic

-- Begin RectangleEnergy

open MeasureTheory

namespace FriezeKannan.Continuum.Proof

lemma cut_energy_identity {f : Sq → ℝ} (hf : MemLp f 2)
    (S T : Set unitInterval) (hS : MeasurableSet S) (hT : MeasurableSet T) (d : ℝ) :
    (∫ p, (f p - cutFun S T d p) ^ 2) =
      (∫ p, f p ^ 2) - 2 * d * rectInt f S T +
        volume.real (S ×ˢ T : Set Sq) * d ^ 2 := by
  classical
  let R : Set Sq := S ×ˢ T
  have hR : MeasurableSet R := hS.prod hT
  have hi : Integrable f := hf.integrable (by norm_num)
  have hc : Integrable (fun p => d ^ 2 - 2 * d * f p) :=
    (integrable_const _).sub (hi.const_mul _)
  have he : (fun p => (f p - cutFun S T d p) ^ 2) =
      (fun p => f p ^ 2 + R.indicator (fun q => d ^ 2 - 2 * d * f q) p) := by
    funext p
    by_cases hp : p ∈ R
    · simp only [cutFun, R, Set.indicator_of_mem hp]
      ring
    · simp only [cutFun, R, Set.indicator_of_notMem hp, sub_zero, add_zero]
  rw [he, integral_add hf.integrable_sq (hc.indicator hR), integral_indicator hR,
    integral_sub (integrable_const _) ((hi.integrableOn).const_mul _),
    integral_const, integral_const_mul]
  simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  change (∫ p, f p ^ 2) + (volume.real R * d ^ 2 - 2 * d * rectInt f S T) = _
  dsimp [R, measureReal_def]
  ring

lemma projection_energy_identity {f : Sq → ℝ} (hf : MemLp f 2)
    (S T : Set unitInterval) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hm : 0 < volume.real (S ×ˢ T : Set Sq)) :
    (∫ p, (f p - cutFun S T (rectInt f S T / volume.real (S ×ˢ T : Set Sq)) p) ^ 2) =
      (∫ p, f p ^ 2) - rectInt f S T ^ 2 / volume.real (S ×ˢ T : Set Sq) := by
  rw [cut_energy_identity hf S T hS hT]
  field_simp [ne_of_gt hm]
  ring

end FriezeKannan.Continuum.Proof
-- End RectangleEnergy

-- Begin RectangleDrop

open MeasureTheory

namespace FriezeKannan.Continuum.Proof

lemma rectangle_energy_drop (f : Sq → ℝ) {w : Sq → ℝ} (hw : MemLp w 2)
    (ε : ℝ) (hε : 0 < ε) (S T : Set unitInterval)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hbad : ε * l2Norm f < |rectInt w S T|) :
    ∃ d : ℝ, MemLp (fun p => w p - cutFun S T d p) 2 ∧
      (∫ p, (w p - cutFun S T d p) ^ 2) ≤
        (∫ p, w p ^ 2) - ε ^ 2 * l2Norm f ^ 2 := by
  have hb : rectInt w S T ≠ 0 := by
    intro h
    rw [h, abs_zero] at hbad
    exact (not_lt_of_ge (mul_nonneg hε.le (l2Norm_nonneg f))) hbad
  have hm : 0 < volume.real (S ×ˢ T : Set Sq) := by
    refine lt_of_le_of_ne (rect_measure_nonneg S T) ?_
    intro h
    exact hb (rectInt_zero_of_measure_zero S T h.symm)
  have hs : ε ^ 2 * l2Norm f ^ 2 < rectInt w S T ^ 2 := by
    have h := (sq_lt_sq₀ (mul_nonneg hε.le (l2Norm_nonneg f))
      (abs_nonneg (rectInt w S T))).2 hbad
    simpa only [mul_pow, sq_abs] using h
  have hd : ε ^ 2 * l2Norm f ^ 2 <
      rectInt w S T ^ 2 / volume.real (S ×ˢ T : Set Sq) := by
    apply (lt_div_iff₀ hm).2
    exact lt_of_le_of_lt
      (mul_le_of_le_one_right (mul_nonneg (sq_nonneg ε) (sq_nonneg (l2Norm f)))
        (rect_measure_le_one S T)) hs
  refine ⟨rectInt w S T / volume.real (S ×ˢ T : Set Sq),
    residual_memLp hw S T hS hT _, ?_⟩
  rw [projection_energy_identity hw S T hS hT hm]
  linarith

end FriezeKannan.Continuum.Proof
-- End RectangleDrop

-- Begin EnergyStopping

namespace FriezeKannan.Continuum.Proof

theorem finite_energy_stopping {X : ℕ → Type*}
    (energy : ∀ n, X n → ℝ) (good : ∀ n, X n → Prop)
    (N : ℕ) (E δ : ℝ)
    (hnonneg : ∀ n x, 0 ≤ energy n x)
    (hinit : ∃ x : X 0, energy 0 x ≤ E)
    (hstep : ∀ n (x : X n), ¬good n x →
      ∃ y : X (n+1), energy (n+1) y ≤ energy n x - δ)
    (hbudget : E < ((N : ℝ)+1)*δ) :
    ∃ n ≤ N, ∃ x : X n, good n x := by
  have reach : ∀ n : ℕ, (∃ j < n, ∃ x : X j, good j x) ∨
      ∃ x : X n, energy n x ≤ E - (n : ℝ)*δ := by
    intro n
    induction n with
    | zero =>
      right
      simpa using hinit
    | succ n ih =>
      rcases ih with ⟨j, hj, x, hx⟩ | ⟨x, hx⟩
      · exact Or.inl ⟨j, by omega, x, hx⟩
      · by_cases hg : good n x
        · exact Or.inl ⟨n, by omega, x, hg⟩
        · obtain ⟨y, hy⟩ := hstep n x hg
          right
          refine ⟨y, ?_⟩
          push_cast
          linarith
  rcases reach (N+1) with ⟨n, hn, x, hx⟩ | ⟨x, hx⟩
  · exact ⟨n, by omega, x, hx⟩
  · have hp := hnonneg (N+1) x
    push_cast at hx
    linarith

end FriezeKannan.Continuum.Proof
-- End EnergyStopping

-- Begin ScalarBudget

namespace FriezeKannan.Continuum.Proof

theorem reciprocal_sq_budget (ε E : ℝ) (hε : 0 < ε) (hE : 0 < E) :
    (⌊1 / ε^2⌋₊ : ℝ) ≤ 1 / ε^2 ∧
      E < ((⌊1 / ε^2⌋₊ : ℝ)+1)*(ε^2*E) := by
  have hsq : 0 < ε^2 := sq_pos_of_pos hε
  refine ⟨Nat.floor_le (by positivity), ?_⟩
  have hf : 1 / ε^2 < (⌊1 / ε^2⌋₊ : ℝ)+1 := Nat.lt_floor_add_one _
  have hm := (div_lt_iff₀ hsq).mp hf
  nlinarith [mul_pos (sub_pos.mpr hm) hE]

end FriezeKannan.Continuum.Proof
-- End ScalarBudget

-- Begin Decomposition

open MeasureTheory
namespace FriezeKannan.Continuum.Proof

theorem decomposition_positive_norm (f : Sq → ℝ) (hf : MemLp f 2)
    (ε : ℝ) (hε : 0 < ε) (hnorm : 0 < l2Norm f) :
    ∃ n : ℕ, (n : ℝ) ≤ 1 / ε^2 ∧ ∃ a : CutFamily n,
      ∀ S T : Set unitInterval, MeasurableSet S → MeasurableSet T →
        |rectInt (a.residual f) S T| ≤ ε*l2Norm f := by
  let E : ℝ := l2Norm f ^ 2
  let energy : ∀ n, CutFamily n → ℝ := fun _ a => ∫ p, (a.residual f p)^2
  let good : ∀ n, CutFamily n → Prop := fun _ a =>
    ∀ S T : Set unitInterval, MeasurableSet S → MeasurableSet T →
      |rectInt (a.residual f) S T| ≤ ε*l2Norm f
  obtain ⟨hfloor, hbudget⟩ := reciprocal_sq_budget ε E hε (sq_pos_of_pos hnorm)
  have hinit : ∃ a : CutFamily 0, energy 0 a ≤ E := by
    refine ⟨CutFamily.empty, ?_⟩
    simp only [energy, CutFamily.residual_empty, E, l2Norm_sq_eq_integral]
    exact le_rfl
  have hstep : ∀ n (a : CutFamily n), ¬good n a →
      ∃ b : CutFamily (n+1), energy (n+1) b ≤ energy n a - ε^2*E := by
    intro n a hbad
    simp only [good, not_forall] at hbad
    obtain ⟨S, T, hbad⟩ := hbad
    push Not at hbad
    obtain ⟨hS, hT, hbad⟩ := hbad
    obtain ⟨d, _, hd⟩ := rectangle_energy_drop f (a.memLp_residual hf) ε hε S T hS hT hbad
    refine ⟨a.append S T d hS hT, ?_⟩
    simpa only [energy, CutFamily.residual_append, E] using hd
  obtain ⟨n, hn, a, ha⟩ := finite_energy_stopping energy good ⌊1/ε^2⌋₊ E (ε^2*E)
    (fun _ a => norm_sq_nonneg (a.residual f)) hinit hstep hbudget
  refine ⟨n, le_trans (by exact_mod_cast hn) hfloor, a, ha⟩

end FriezeKannan.Continuum.Proof
-- End Decomposition

-- Begin RootAssembly

open MeasureTheory
namespace FriezeKannan.Continuum
open Proof

theorem theorem_12 (f : Sq → ℝ) (hf : MemLp f 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ, (s : ℝ) ≤ 1 / ε ^ 2 ∧
      ∃ (Ss Ts : Fin s → Set unitInterval) (d : Fin s → ℝ),
        (∀ t, MeasurableSet (Ss t) ∧ MeasurableSet (Ts t)) ∧
        ∀ S T : Set unitInterval, MeasurableSet S → MeasurableSet T →
          |rectInt (fun p => f p - cutFunSum Ss Ts d p) S T| ≤ ε * l2Norm f := by
  by_cases hz : l2Norm f = 0
  · refine ⟨0, by norm_num; positivity, Fin.elim0, Fin.elim0, Fin.elim0,
      (fun i => Fin.elim0 i), ?_⟩
    intro S T _ _
    simpa [cutFunSum, hz] using (norm_zero_rectInt hf hz S T)
  · obtain ⟨n, hn, a, ha⟩ := decomposition_positive_norm f hf ε hε
      (lt_of_le_of_ne (l2Norm_nonneg f) (Ne.symm hz))
    exact ⟨n, hn, a.left, a.right, a.coeff, a.measurable, ha⟩

end FriezeKannan.Continuum
-- End RootAssembly

-- Begin Solution

open MeasureTheory
open FriezeKannan.Continuum

theorem solution (f : Sq → ℝ) (hf : MemLp f 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ, (s : ℝ) ≤ 1 / ε ^ 2 ∧
      ∃ (Ss Ts : Fin s → Set unitInterval) (d : Fin s → ℝ),
        (∀ t, MeasurableSet (Ss t) ∧ MeasurableSet (Ts t)) ∧
        ∀ S T : Set unitInterval, MeasurableSet S → MeasurableSet T →
          |rectInt (fun p => f p - cutFunSum Ss Ts d p) S T| ≤ ε * l2Norm f := FriezeKannan.Continuum.theorem_12 f hf ε hε

-- End Solution
