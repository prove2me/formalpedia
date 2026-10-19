-- Prove2me | solution 1 for CauchyRiemannIndex.joined_of_fundamentalSolution_close
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T14:12:04.13555+00:00
-- url     : https://prove2.me/submissions/c571777b-81cf-47ee-8a0d-11136704734c

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Order.Filter.Basic
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Theorems.Thm_CauchyRiemannIndex_symLoop_of_symplecticPath_family
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Rational interpolation `C(l, A) = ((1-l)A + (1+l))⁻¹ ((1+l)A + (1-l))` in `Sp(2n)`. -/

open CauchyRiemannIndex Matrix

namespace CRJ3C

variable {n : ℕ}

theorem jJ : J₀ n * J₀ n = -1 := Matrix.J_squared _ _

theorem jT : (J₀ n)ᵀ = -J₀ n := Matrix.J_transpose _ _

/-- The symplectic inverse `-J Xᵀ J`. -/
def sinv (X : Mat n) : Mat n := -J₀ n * Xᵀ * J₀ n

theorem sinv_mem {X : Mat n} (h : IsSymplectic X) : IsSymplectic (sinv X) :=
  ((⟨X, h⟩ : symplecticGroup (Fin n) ℝ)⁻¹).2

theorem sinv_mul {X : Mat n} (h : IsSymplectic X) : sinv X * X = 1 := by
  have := SymplecticGroup.inv_left_mul_aux h
  simpa [sinv, neg_mul] using this

theorem mul_sinv {X : Mat n} (h : IsSymplectic X) : X * sinv X = 1 :=
  mul_eq_one_comm.1 (sinv_mul h)

theorem sinv_one : sinv (1 : Mat n) = 1 := by
  simp [sinv, neg_mul, jJ]

def Mf (l : ℝ) (A : Mat n) : Mat n := (1 - l) • A + (1 + l) • (1 : Mat n)

def Nf (l : ℝ) (A : Mat n) : Mat n := (1 + l) • A + (1 - l) • (1 : Mat n)

/-- The interpolation `C(l, A)`. -/
noncomputable def Cf (l : ℝ) (A : Mat n) : Mat n := Ring.inverse (Mf l A) * Nf l A

/-- `F(l, X, Y) = X C(l, X⁻¹ Y)`. -/
noncomputable def Ff (p : ℝ × Mat n × Mat n) : Mat n := p.2.1 * Cf p.1 (sinv p.2.1 * p.2.2)

/-- Where the interpolation is defined. -/
def Uset (n : ℕ) : Set (ℝ × Mat n × Mat n) := {p | IsUnit (Mf p.1 (sinv p.2.1 * p.2.2))}

theorem NJN {l : ℝ} {A : Mat n} (hA : IsSymplectic A) :
    Nf l A * J₀ n * (Nf l A)ᵀ = Mf l A * J₀ n * (Mf l A)ᵀ := by
  have h := SymplecticGroup.mem_iff.1 hA
  simp only [Mf, Nf, transpose_add, transpose_smul, transpose_one, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, smul_add, h]
  module

theorem Cf_mem {l : ℝ} {A : Mat n} (hA : IsSymplectic A) (hu : IsUnit (Mf l A)) :
    IsSymplectic (Cf l A) := by
  unfold IsSymplectic
  rw [SymplecticGroup.mem_iff]
  have hi : Ring.inverse (Mf l A) * Mf l A = 1 := Ring.inverse_mul_cancel _ hu
  have hiT : (Mf l A)ᵀ * (Ring.inverse (Mf l A))ᵀ = 1 := by
    rw [← transpose_mul, hi, transpose_one]
  calc Cf l A * J₀ n * (Cf l A)ᵀ
      = Ring.inverse (Mf l A) * (Nf l A * J₀ n * (Nf l A)ᵀ) * (Ring.inverse (Mf l A))ᵀ := by
        simp only [Cf, transpose_mul, Matrix.mul_assoc]
    _ = (Ring.inverse (Mf l A) * Mf l A) * J₀ n * ((Mf l A)ᵀ * (Ring.inverse (Mf l A))ᵀ) := by
        rw [NJN hA]; simp only [Matrix.mul_assoc]
    _ = J₀ n := by rw [hi, hiT, Matrix.one_mul, Matrix.mul_one]

theorem Ff_mem {p : ℝ × Mat n × Mat n} (hX : IsSymplectic p.2.1) (hY : IsSymplectic p.2.2)
    (hu : p ∈ Uset n) : IsSymplectic (Ff p) :=
  Submonoid.mul_mem _ hX (Cf_mem (Submonoid.mul_mem _ (sinv_mem hX) hY) hu)

/-- `2 • 1` as a unit. -/
noncomputable def twoU : (Mat n)ˣ :=
  ⟨(2 : ℝ) • 1, (1 / 2 : ℝ) • 1, by simp [smul_smul], by simp [smul_smul]⟩

theorem two_isUnit : IsUnit ((2 : ℝ) • (1 : Mat n)) := ⟨twoU, rfl⟩

theorem inverse_two : Ring.inverse ((2 : ℝ) • (1 : Mat n)) = (1 / 2 : ℝ) • 1 :=
  Ring.inverse_unit (twoU (n := n))

theorem Mf_one (l : ℝ) : Mf l (1 : Mat n) = (2 : ℝ) • 1 := by
  simp only [Mf, ← add_smul]; ring_nf

theorem Nf_one (l : ℝ) : Nf l (1 : Mat n) = (2 : ℝ) • 1 := by
  simp only [Nf, ← add_smul]; ring_nf

theorem Ff_self (l : ℝ) {X : Mat n} (hX : IsSymplectic X) : Ff (l, X, X) = X := by
  simp only [Ff, Cf, sinv_mul hX, Mf_one, Nf_one, Ring.inverse_mul_cancel _ two_isUnit,
    Matrix.mul_one]

theorem Ff_zero {X Y : Mat n} : Ff (0, X, Y) = X ∨ ¬ ((0, X, Y) ∈ Uset n) := by
  by_cases hu : (0, X, Y) ∈ Uset n
  · left
    have hMN : Mf 0 (sinv X * Y) = Nf 0 (sinv X * Y) := by simp [Mf, Nf, add_comm]
    simp only [Ff, Cf]
    rw [← hMN, Ring.inverse_mul_cancel _ hu, Matrix.mul_one]
  · exact Or.inr hu

theorem Ff_zero' {X Y : Mat n} (hu : (0, X, Y) ∈ Uset n) : Ff (0, X, Y) = X :=
  (Ff_zero (X := X) (Y := Y)).resolve_right (not_not.2 hu)

theorem Ff_one {X Y : Mat n} (hX : IsSymplectic X) : Ff (1, X, Y) = Y := by
  have hM : Mf 1 (sinv X * Y) = (2 : ℝ) • 1 := by norm_num [Mf]
  have hN : Nf 1 (sinv X * Y) = (2 : ℝ) • (sinv X * Y) := by norm_num [Nf]
  simp only [Ff, Cf, hM, hN, inverse_two, smul_mul_assoc, Matrix.one_mul, smul_smul]
  norm_num
  rw [← Matrix.mul_assoc, mul_sinv hX, Matrix.one_mul]

/-! ### Entrywise neighbourhoods (sup metric) -/

section Sup

theorem mem_of_entry {δ : ℝ} (hδ : 0 < δ) {p k : ℝ × Mat n × Mat n} (h1 : |p.1 - k.1| < δ)
    (h2 : ∀ i j, |p.2.1 i j - k.2.1 i j| < δ) (h3 : ∀ i j, |p.2.2 i j - k.2.2 i j| < δ) :
    letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
    dist p k < δ := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  rw [Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff, Real.dist_eq, dist_eq_norm,
    dist_eq_norm, Matrix.norm_lt_iff hδ, Matrix.norm_lt_iff hδ]
  exact ⟨h1, fun i j => by simpa [Real.norm_eq_abs] using h2 i j,
    fun i j => by simpa [Real.norm_eq_abs] using h3 i j⟩

theorem exists_entry_nbhd {K U : Set (ℝ × Mat n × Mat n)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ δ > 0, ∀ k ∈ K, ∀ p : ℝ × Mat n × Mat n, |p.1 - k.1| < δ →
      (∀ i j, |p.2.1 i j - k.2.1 i j| < δ) → (∀ i j, |p.2.2 i j - k.2.2 i j| < δ) → p ∈ U := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hU hKU
  exact ⟨δ, hδ, fun k hk p h1 h2 h3 =>
    hsub (Metric.mem_thickening_iff.2 ⟨k, hk, mem_of_entry hδ h1 h2 h3⟩)⟩

theorem exists_entry_close {K : Set (ℝ × Mat n × Mat n)} (hK : IsCompact K)
    (f : ℝ × Mat n × Mat n → Mat n) (hf : ∀ k ∈ K, ContinuousAt f k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ k ∈ K, ∀ p : ℝ × Mat n × Mat n, |p.1 - k.1| < δ →
      (∀ i j, |p.2.1 i j - k.2.1 i j| < δ) → (∀ i j, |p.2.2 i j - k.2.2 i j| < δ) →
      ∀ i j, |f p i j - f k i j| < ε := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  have hu := hK.uniformContinuousAt_of_continuousAt f hf (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hδu⟩ := Metric.mem_uniformity_dist.1 hu
  refine ⟨δ, hδ, fun k hk p h1 h2 h3 i j => ?_⟩
  have hd : dist k p < δ := by rw [dist_comm]; exact mem_of_entry hδ h1 h2 h3
  have h := hδu hd hk
  simp only [Set.mem_setOf_eq] at h
  rw [dist_comm, dist_eq_norm] at h
  have := (Matrix.norm_entry_le_entrywise_sup_norm (f p - f k) (i := i) (j := j)).trans_lt h
  simpa [Real.norm_eq_abs] using this

end Sup

/-! ### Analysis (operator norm) -/

section Analytic

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

local instance : CompleteSpace (Mat n) := FiniteDimensional.complete ℝ (Mat n)

/-- Transposition as a continuous linear map. -/
noncomputable def trL : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (Fin n ⊕ Fin n)
    (Fin n ⊕ Fin n) ℝ ℝ).toLinearMap

theorem contDiff_A : ContDiff ℝ 1 (fun p : ℝ × Mat n × Mat n => sinv p.2.1 * p.2.2) := by
  have hT : ContDiff ℝ 1 (fun p : ℝ × Mat n × Mat n => (p.2.1)ᵀ) :=
    (trL (n := n)).contDiff.comp contDiff_snd.fst
  exact ((contDiff_const.mul hT).mul contDiff_const).mul contDiff_snd.snd

theorem contDiff_Mf : ContDiff ℝ 1 (fun p : ℝ × Mat n × Mat n => Mf p.1 (sinv p.2.1 * p.2.2)) :=
  ((contDiff_const.sub contDiff_fst).smul contDiff_A).add
    ((contDiff_const.add contDiff_fst).smul contDiff_const)

theorem contDiff_Nf : ContDiff ℝ 1 (fun p : ℝ × Mat n × Mat n => Nf p.1 (sinv p.2.1 * p.2.2)) :=
  ((contDiff_const.add contDiff_fst).smul contDiff_A).add
    ((contDiff_const.sub contDiff_fst).smul contDiff_const)

theorem isOpen_Uset : IsOpen (Uset n) :=
  Units.isOpen.preimage contDiff_Mf.continuous

theorem contDiffOn_Ff : ContDiffOn ℝ 1 (Ff (n := n)) (Uset n) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨u, hu⟩ := hp
  have hinv : ContDiffAt ℝ 1 (fun p : ℝ × Mat n × Mat n =>
      Ring.inverse (Mf p.1 (sinv p.2.1 * p.2.2))) p := by
    have := contDiffAt_ringInverse ℝ (n := 1) u
    rw [hu] at this
    exact this.comp p contDiff_Mf.contDiffAt
  exact contDiffAt_snd.fst.mul (hinv.mul contDiff_Nf.contDiffAt)

end Analytic

end CRJ3C

/-! Clamping a `C¹` path to `[0, 1]` when its derivative vanishes at both ends. -/

open Filter Topology Set

namespace CRJ3C

/-- `t ↦ max 0 (min t 1)`. -/
def cl (t : ℝ) : ℝ := max 0 (min t 1)

theorem cl_mem (t : ℝ) : cl t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem cl_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : cl t = t := by
  simp [cl, min_eq_left ht.2, max_eq_right ht.1]

theorem cl_of_nonpos {t : ℝ} (ht : t ≤ 0) : cl t = 0 := by
  simp [cl, max_eq_left (min_le_of_left_le ht)]

theorem cl_of_one_le {t : ℝ} (ht : 1 ≤ t) : cl t = 1 := by
  simp [cl, min_eq_right ht]

theorem hasDerivAt_comp_cl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E}
    (hf : ∀ t, HasDerivAt f (f' t) t) (h0 : f' 0 = 0) (h1 : f' 1 = 0) (t : ℝ) :
    HasDerivAt (fun s => f (cl s)) (f' (cl t)) t := by
  have hc0 : HasDerivWithinAt (fun s => f (cl s)) 0 (Iic 0) 0 :=
    (hasDerivWithinAt_const 0 (Iic 0) (f 0)).congr (fun s hs => by rw [cl_of_nonpos hs])
      (by rw [cl_of_nonpos le_rfl])
  have hc1 : HasDerivWithinAt (fun s => f (cl s)) 0 (Ici 1) 1 :=
    (hasDerivWithinAt_const 1 (Ici 1) (f 1)).congr (fun s hs => by rw [cl_of_one_le hs])
      (by rw [cl_of_one_le le_rfl])
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [cl_of_nonpos ht.le, h0]
    have hev : (fun s => f (cl s)) =ᶠ[𝓝 t] fun _ => f 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      rw [cl_of_nonpos (le_of_lt hs)]
    exact (hasDerivAt_const t (f 0)).congr_of_eventuallyEq hev
  · rw [cl_of_nonpos le_rfl, h0]
    have hr : HasDerivWithinAt (fun s => f (cl s)) 0 (Ici 0) 0 := by
      have := (hf 0).hasDerivWithinAt (s := Ici 0)
      rw [h0] at this
      refine this.congr_of_eventuallyEq ?_ (by rw [cl_of_nonpos le_rfl])
      filter_upwards [Ico_mem_nhdsGE (zero_lt_one' ℝ)] with s hs
      rw [cl_of_mem ⟨hs.1, hs.2.le⟩]
    have := hc0.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  rcases lt_trichotomy t 1 with ht1 | rfl | ht1
  · rw [cl_of_mem ⟨ht.le, ht1.le⟩]
    have hev : (fun s => f (cl s)) =ᶠ[𝓝 t] f := by
      filter_upwards [Ioo_mem_nhds ht ht1] with s hs
      rw [cl_of_mem ⟨hs.1.le, hs.2.le⟩]
    exact (hf t).congr_of_eventuallyEq hev
  · rw [cl_of_one_le le_rfl, h1]
    have hl : HasDerivWithinAt (fun s => f (cl s)) 0 (Iic 1) 1 := by
      have := (hf 1).hasDerivWithinAt (s := Iic 1)
      rw [h1] at this
      refine this.congr_of_eventuallyEq ?_ (by rw [cl_of_one_le le_rfl])
      filter_upwards [Ioc_mem_nhdsLE (zero_lt_one' ℝ)] with s hs
      rw [cl_of_mem ⟨hs.1.le, hs.2⟩]
    have := hl.union hc1
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rw [cl_of_one_le ht1.le, h1]
    have hev : (fun s => f (cl s)) =ᶠ[𝓝 t] fun _ => f 1 := by
      filter_upwards [Ioi_mem_nhds ht1] with s hs
      rw [cl_of_one_le (le_of_lt hs)]
    exact (hasDerivAt_const t (f 1)).congr_of_eventuallyEq hev

end CRJ3C

open CauchyRiemannIndex Matrix

namespace CRJ3C

variable {n : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

local instance : CompleteSpace (Mat n) := FiniteDimensional.complete ℝ (Mat n)

theorem lv_fund {Ψ S : Mat n} (hΨ : IsSymplectic Ψ) :
    J₀ n * (J₀ n * S * Ψ) * J₀ n * Ψᵀ * J₀ n = S := by
  have h := SymplecticGroup.mem_iff.1 hΨ
  calc _ = (J₀ n * J₀ n) * S * (Ψ * J₀ n * Ψᵀ) * J₀ n := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h, jJ]; simp [Matrix.mul_assoc, jJ]

theorem periodic_fract {S : ℝ → Mat n} (hS : Function.Periodic S 1) (t : ℝ) :
    S (Int.fract t) = S t := by
  have := hS.sub_int_mul_eq (n := ⌊t⌋) (x := t)
  rw [mul_one] at this
  rw [Int.fract, this]

theorem fract_mem' (t : ℝ) : Int.fract t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

theorem fund_continuous {S Ψ : ℝ → Mat n} (hΨ : IsFundamentalSolution S Ψ) : Continuous Ψ :=
  continuous_iff_continuousAt.2 fun t => (hΨ.2 t).continuousAt

theorem continuous_cl : Continuous cl := by
  unfold cl; exact continuous_const.max (continuous_id.min continuous_const)

theorem d2 (n : ℕ) (ψ : C(unitInterval, Mat n))
    (hψ : ∀ t, IsSymplectic (ψ t)) (hψ1 : (1 - ψ 1).det ≠ 0) :
    ∃ ε > 0, ∀ S S' Ψ Ψ' : ℝ → Mat n, IsSymLoop S → IsSymLoop S' → IsNondegenerate S →
      IsNondegenerate S' → S 0 = 0 → S' 0 = 0 → IsFundamentalSolution S Ψ →
      IsFundamentalSolution S' Ψ' → (∀ t : unitInterval, ∀ i j, |Ψ t i j - ψ t i j| < ε) →
      (∀ t : unitInterval, ∀ i j, |Ψ' t i j - ψ t i j| < ε) →
      ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S t) ∧ (∀ t, H (1, t) = S' t) ∧
        ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) := by
  let κ : unitInterval × unitInterval → ℝ × Mat n × Mat n := fun q => ((q.1 : ℝ), ψ q.2, ψ q.2)
  have hκ : Continuous κ := (continuous_subtype_val.comp continuous_fst).prodMk
    ((ψ.continuous.comp continuous_snd).prodMk (ψ.continuous.comp continuous_snd))
  have hKU : Set.range κ ⊆ Uset n := by
    rintro _ ⟨q, rfl⟩
    show IsUnit (Mf _ (sinv (ψ q.2) * ψ q.2))
    rw [sinv_mul (hψ _), Mf_one]; exact two_isUnit
  obtain ⟨δ₁, hδ₁, hU⟩ := exists_entry_nbhd (isCompact_range hκ) isOpen_Uset hKU
  let V : Set (ℝ × Mat n × Mat n) := Uset n ∩ Ff ⁻¹' {X | (1 - X).det ≠ 0}
  have hV : IsOpen V := contDiffOn_Ff.continuousOn.isOpen_inter_preimage isOpen_Uset
    (isOpen_ne_fun (continuous_const.sub continuous_id).matrix_det continuous_const)
  let κ₁ : unitInterval → ℝ × Mat n × Mat n := fun l => ((l : ℝ), ψ 1, ψ 1)
  have hκ₁ : Continuous κ₁ := continuous_subtype_val.prodMk continuous_const
  have hK₁V : Set.range κ₁ ⊆ V := by
    rintro _ ⟨l, rfl⟩
    refine ⟨hKU ⟨(l, 1), rfl⟩, ?_⟩
    show (1 - Ff ((l : ℝ), ψ 1, ψ 1)).det ≠ 0
    rw [Ff_self _ (hψ 1)]; exact hψ1
  obtain ⟨δ₂, hδ₂, hV'⟩ := exists_entry_nbhd (isCompact_range hκ₁) hV hK₁V
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro S S' Ψ Ψ' hS hS' hn hn' h0 h0' hΨ hΨ' hc hc'
  have hΨs := fundamentalSolution_symplectic n S hS.2.2 Ψ hΨ
  have hΨs' := fundamentalSolution_symplectic n S' hS'.2.2 Ψ' hΨ'
  have hS1 : S 1 = 0 := by have := hS.2.1 0; rw [zero_add] at this; rw [this, h0]
  have hS1' : S' 1 = 0 := by have := hS'.2.1 0; rw [zero_add] at this; rw [this, h0']
  have e0 : cl 0 = 0 := cl_of_nonpos le_rfl
  have e1 : cl 1 = 1 := cl_of_one_le le_rfl
  let P : ℝ → Mat n := fun t => Ψ (cl t)
  let Q : ℝ → Mat n := fun t => Ψ' (cl t)
  let P' : ℝ → Mat n := fun t => J₀ n * S (cl t) * Ψ (cl t)
  let Q' : ℝ → Mat n := fun t => J₀ n * S' (cl t) * Ψ' (cl t)
  have hP : ∀ t, HasDerivAt P (P' t) t := hasDerivAt_comp_cl (f' := fun t => J₀ n * S t * Ψ t)
    hΨ.2 (by simp [h0]) (by simp [hS1])
  have hQ : ∀ t, HasDerivAt Q (Q' t) t := hasDerivAt_comp_cl (f' := fun t => J₀ n * S' t * Ψ' t)
    hΨ'.2 (by simp [h0']) (by simp [hS1'])
  have hPc : Continuous P := (fund_continuous hΨ).comp continuous_cl
  have hQc : Continuous Q := (fund_continuous hΨ').comp continuous_cl
  have hP'c : Continuous P' :=
    ((continuous_const.mul (hS.1.comp continuous_cl)).mul hPc)
  have hQ'c : Continuous Q' :=
    ((continuous_const.mul (hS'.1.comp continuous_cl)).mul hQc)
  let c : unitInterval × ℝ → ℝ × Mat n × Mat n := fun p => ((p.1 : ℝ), P p.2, Q p.2)
  have hcc : Continuous c := (continuous_subtype_val.comp continuous_fst).prodMk
    ((hPc.comp continuous_snd).prodMk (hQc.comp continuous_snd))
  have hmem : ∀ (l : unitInterval) (t : ℝ), ((l : ℝ), P t, Q t) ∈ Uset n := fun l t =>
    hU (κ (l, ⟨cl t, cl_mem t⟩)) ⟨_, rfl⟩ ((l : ℝ), P t, Q t) (by simpa [κ] using hδ₁)
      (fun i j => (hc ⟨cl t, cl_mem t⟩ i j).trans_le (min_le_left _ _))
      (fun i j => (hc' ⟨cl t, cl_mem t⟩ i j).trans_le (min_le_left _ _))
  have hmem1 : ∀ l : unitInterval, ((l : ℝ), P 1, Q 1) ∈ V := fun l =>
    hV' (κ₁ l) ⟨l, rfl⟩ ((l : ℝ), P 1, Q 1) (by simpa [κ₁] using hδ₂)
      (fun i j => by
        have := (hc 1 i j).trans_le (min_le_right _ _)
        simpa [P, e1] using this)
      (fun i j => by
        have := (hc' 1 i j).trans_le (min_le_right _ _)
        simpa [Q, e1] using this)
  let φ : unitInterval → ℝ → Mat n := fun l t => Ff ((l : ℝ), P t, Q t)
  let φ' : unitInterval → ℝ → Mat n := fun l t =>
    fderiv ℝ Ff ((l : ℝ), P t, Q t) (0, P' t, Q' t)
  have hdiff : ∀ (l : unitInterval) t, DifferentiableAt ℝ Ff ((l : ℝ), P t, Q t) := fun l t =>
    (contDiffOn_Ff.contDiffAt (isOpen_Uset.mem_nhds (hmem l t))).differentiableAt one_ne_zero
  have hd : ∀ l t, HasDerivAt (φ l) (φ' l t) t := fun l t => by
    have h1 := (hdiff l t).hasFDerivAt
    have h2 : HasDerivAt (fun x => ((l : ℝ), P x, Q x)) ((0 : ℝ), P' t, Q' t) t :=
      HasDerivAt.prodMk (hasDerivAt_const t (l : ℝ)) (HasDerivAt.prodMk (hP t) (hQ t))
    exact h1.comp_hasDerivAt t h2
  have hφc : Continuous fun p : unitInterval × ℝ => φ p.1 p.2 :=
    contDiffOn_Ff.continuousOn.comp_continuous hcc (fun p => hmem p.1 p.2)
  have hφ'c : Continuous fun p : unitInterval × ℝ => φ' p.1 p.2 :=
    ((contDiffOn_Ff.continuousOn_fderiv_of_isOpen isOpen_Uset le_rfl).comp_continuous hcc
      (fun p => hmem p.1 p.2)).clm_apply
      (continuous_const.prodMk ((hP'c.comp continuous_snd).prodMk (hQ'c.comp continuous_snd)))
  have hs : ∀ l, ∀ t ∈ Set.Icc (0 : ℝ) 1, IsSymplectic (φ l t) := fun l t _ =>
    Ff_mem (hΨs _) (hΨs' _) (hmem l t)
  have h0φ : ∀ l, φ l 0 = 1 := fun l => by
    show Ff ((l : ℝ), Ψ (cl 0), Ψ' (cl 0)) = 1
    rw [e0, hΨ.1, hΨ'.1]; exact Ff_self _ (Submonoid.one_mem _)
  have hd0 : ∀ l, φ' l 0 = 0 := fun l => by
    show fderiv ℝ Ff _ (0, P' 0, Q' 0) = 0
    have a : P' 0 = 0 := by simp [P', e0, h0]
    have b : Q' 0 = 0 := by simp [Q', e0, h0']
    rw [a, b, Prod.mk_zero_zero, Prod.mk_zero_zero, map_zero]
  have hd1 : ∀ l, φ' l 1 = 0 := fun l => by
    show fderiv ℝ Ff _ (0, P' 1, Q' 1) = 0
    have a : P' 1 = 0 := by simp [P', e1, hS1]
    have b : Q' 1 = 0 := by simp [Q', e1, hS1']
    rw [a, b, Prod.mk_zero_zero, Prod.mk_zero_zero, map_zero]
  have hnφ : ∀ l, (1 - φ l 1).det ≠ 0 := fun l => (hmem1 l).2
  obtain ⟨H, hHf, hH⟩ := symLoop_of_symplecticPath_family n φ φ' hφc hφ'c hd hs h0φ hd0 hd1 hnφ
  have hφ0 : φ 0 = P := funext fun t => Ff_zero' (hmem 0 t)
  have hφ1 : φ 1 = Q := funext fun t => Ff_one (hΨs _)
  have hφ'0 : ∀ t, φ' 0 t = P' t := fun t => by
    have := hd 0 t; rw [hφ0] at this; exact this.unique (hP t)
  have hφ'1 : ∀ t, φ' 1 t = Q' t := fun t => by
    have := hd 1 t; rw [hφ1] at this; exact this.unique (hQ t)
  refine ⟨H, fun t => ?_, fun t => ?_, fun τ => ⟨(hH τ).1, (hH τ).2.1⟩⟩
  · rw [hHf, hφ'0, hφ0]
    simp only [P, P', cl_of_mem (fract_mem' t)]
    rw [lv_fund (hΨs _), periodic_fract hS.2.1]
  · rw [hHf, hφ'1, hφ1]
    simp only [Q, Q', cl_of_mem (fract_mem' t)]
    rw [lv_fund (hΨs' _), periodic_fract hS'.2.1]

end CRJ3C

theorem solution (n : ℕ) (ψ : C(unitInterval, Mat n))
    (hψ : ∀ t, IsSymplectic (ψ t)) (hψ1 : (1 - ψ 1).det ≠ 0) :
    ∃ ε > 0, ∀ S S' Ψ Ψ' : ℝ → Mat n, IsSymLoop S → IsSymLoop S' → IsNondegenerate S →
      IsNondegenerate S' → S 0 = 0 → S' 0 = 0 → IsFundamentalSolution S Ψ →
      IsFundamentalSolution S' Ψ' → (∀ t : unitInterval, ∀ i j, |Ψ t i j - ψ t i j| < ε) →
      (∀ t : unitInterval, ∀ i j, |Ψ' t i j - ψ t i j| < ε) →
      ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S t) ∧ (∀ t, H (1, t) = S' t) ∧
        ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) :=
  CRJ3C.d2 n ψ hψ hψ1
