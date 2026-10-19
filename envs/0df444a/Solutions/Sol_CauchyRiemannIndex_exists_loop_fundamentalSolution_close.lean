-- Prove2me | solution 1 for CauchyRiemannIndex.exists_loop_fundamentalSolution_close
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T14:21:19.506446+00:00
-- url     : https://prove2.me/submissions/f8662fbd-044f-4eda-b402-892d9242f536

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Order.Filter.Basic
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_CauchyRiemannIndex_symLoop_of_symplecticPath_family
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.UniformSpace.HeineCantor

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

theorem path_uc (ψ : C(unitInterval, Mat n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ s t : unitInterval, dist s t < η → ∀ i j, |ψ s i j - ψ t i j| < δ := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  have hu := CompactSpace.uniformContinuous_of_continuous ψ.continuous
  rw [Metric.uniformContinuous_iff] at hu
  obtain ⟨η, hη, h⟩ := hu δ hδ
  refine ⟨η, hη, fun s t hst i j => ?_⟩
  have h2 := h hst
  rw [dist_eq_norm] at h2
  have := (Matrix.norm_entry_le_entrywise_sup_norm (ψ s - ψ t) (i := i) (j := j)).trans_lt h2
  simpa [Real.norm_eq_abs] using this

theorem list_prod_mem {L : List ℕ} {f : ℕ → Mat n} (h : ∀ k ∈ L, IsSymplectic (f k)) :
    IsSymplectic ((L.map f).prod) := by
  induction L with
  | nil => exact Submonoid.one_mem _
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact Submonoid.mul_mem _ (h a (by simp)) (ih fun k hk => h k (by simp [hk]))

theorem exists_cell {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j < N, (j : ℝ) ≤ N * t ∧ N * t ≤ j + 1 := by
  have hNt : 0 ≤ (N : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht.1
  by_cases h : ⌊(N : ℝ) * t⌋₊ < N
  · exact ⟨_, h, Nat.floor_le hNt, (Nat.lt_floor_add_one _).le⟩
  · refine ⟨N - 1, by omega, ?_, ?_⟩
    · have : ((N - 1 : ℕ) : ℝ) ≤ ⌊(N : ℝ) * t⌋₊ := by exact_mod_cast (by omega : N - 1 ≤ _)
      exact this.trans (Nat.floor_le hNt)
    · rw [Nat.cast_sub hN, Nat.cast_one, sub_add_cancel]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) ht.2

section An

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

local instance : CompleteSpace (Mat n) := FiniteDimensional.complete ℝ (Mat n)

theorem contDiff_list_prod {L : List ℕ} {f : ℕ → ℝ → Mat n}
    (h : ∀ k ∈ L, ContDiff ℝ 1 (f k)) :
    ContDiff ℝ 1 (fun t => (L.map (fun k => f k t)).prod) := by
  induction L with
  | nil => simpa using contDiff_const
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h a (by simp)).mul (ih fun k hk => h k (by simp [hk]))

theorem d3 (n : ℕ) (ψ : C(unitInterval, Mat n)) (hψ : ∀ t, IsSymplectic (ψ t))
    (hψ0 : ψ 0 = 1) (hψ1 : (1 - ψ 1).det ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ S Ψ : ℝ → Mat n, IsSymLoop S ∧ IsNondegenerate S ∧ S 0 = 0 ∧
      IsFundamentalSolution S Ψ ∧ ∀ t : unitInterval, ∀ i j, |Ψ t i j - ψ t i j| < ε := by
  let κ : unitInterval × unitInterval → ℝ × Mat n × Mat n := fun q => ((q.1 : ℝ), ψ q.2, ψ q.2)
  have hκ : Continuous κ := (continuous_subtype_val.comp continuous_fst).prodMk
    ((ψ.continuous.comp continuous_snd).prodMk (ψ.continuous.comp continuous_snd))
  have hKU : Set.range κ ⊆ Uset n := by
    rintro _ ⟨q, rfl⟩
    show IsUnit (Mf _ (sinv (ψ q.2) * ψ q.2))
    rw [sinv_mul (hψ _), Mf_one]; exact two_isUnit
  obtain ⟨δ₁, hδ₁, hU⟩ := exists_entry_nbhd (isCompact_range hκ) isOpen_Uset hKU
  obtain ⟨δ₂, hδ₂, hC⟩ := exists_entry_close (isCompact_range hκ) Ff
    (fun k hk => contDiffOn_Ff.continuousOn.continuousAt (isOpen_Uset.mem_nhds (hKU hk)))
    (half_pos hε)
  obtain ⟨η, hη, hψu⟩ := path_uc ψ (lt_min (lt_min hδ₁ hδ₂) (half_pos hε))
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  have hNr : (0 : ℝ) < N := (one_div_pos.2 hη).trans hN
  have hN0 : 0 < N := by exact_mod_cast hNr
  have hNη : 1 / (N : ℝ) < η := by
    rw [div_lt_iff₀ hNr]; rw [div_lt_iff₀ hη] at hN; linarith
  let node : ℕ → unitInterval := fun k => ⟨cl (k / N), cl_mem _⟩
  have hnode : ∀ k ≤ N, (node k : ℝ) = k / N := fun k hk =>
    cl_of_mem ⟨by positivity, by rw [div_le_one hNr]; exact_mod_cast hk⟩
  let g : ℕ → Mat n := fun k => ψ (node k)
  have hg0 : g 0 = 1 := by
    have : node 0 = 0 := Subtype.ext (by simp [node, cl_of_nonpos])
    show ψ (node 0) = 1; rw [this, hψ0]
  have hgN : g N = ψ 1 := by
    have : node N = 1 := Subtype.ext (by
      show cl ((N : ℝ) / N) = 1; rw [div_self hNr.ne']; exact cl_of_one_le le_rfl)
    show ψ (node N) = ψ 1; rw [this]
  let A : ℕ → Mat n := fun k => sinv (g k) * g (k + 1)
  have hA : ∀ k, IsSymplectic (A k) := fun k => Submonoid.mul_mem _ (sinv_mem (hψ _)) (hψ _)
  have hgA : ∀ k, g k * A k = g (k + 1) := fun k => by
    show g k * (sinv (g k) * g (k + 1)) = _
    rw [← Matrix.mul_assoc, mul_sinv (hψ _), Matrix.one_mul]
  have hclose : ∀ k < N, ∀ i j, |g (k + 1) i j - g k i j| < min (min δ₁ δ₂) (ε / 2) :=
    fun k hk i j => hψu (node (k + 1)) (node k) (by
      rw [Subtype.dist_eq, hnode _ hk, hnode _ hk.le, Real.dist_eq]
      rw [show ((k + 1 : ℕ) : ℝ) / N - k / N = 1 / N by push_cast; ring]
      rw [abs_of_pos (by positivity)]; exact hNη) i j
  have hunit : ∀ k < N, ∀ s ∈ Set.Icc (0 : ℝ) 1, (s, g k, g (k + 1)) ∈ Uset n :=
    fun k hk s hs => hU (κ (⟨s, hs⟩, node k)) ⟨_, rfl⟩ (s, g k, g (k + 1))
      (by simpa [κ] using hδ₁) (fun i j => by simpa [κ, g] using hδ₁)
      (fun i j => (hclose k hk i j).trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  let σ : ℝ → ℝ := Real.smoothTransition
  have hσ : ∀ x, σ x ∈ Set.Icc (0 : ℝ) 1 := fun x =>
    ⟨Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x⟩
  let fac : ℕ → ℝ → Mat n := fun k t => Ff (σ (N * t - k), 1, A k)
  have hfacU : ∀ k < N, ∀ t, (σ (N * t - k), (1 : Mat n), A k) ∈ Uset n := fun k hk t => by
    have := hunit k hk _ (hσ (N * t - k))
    show IsUnit (Mf _ (sinv 1 * A k)); rw [sinv_one, Matrix.one_mul]; exact this
  have hfac1 : ∀ (k : ℕ) (t : ℝ), 1 ≤ (N : ℝ) * t - k → fac k t = A k := fun k t h => by
    show Ff (σ _, 1, A k) = A k
    rw [show σ (N * t - k) = 1 from Real.smoothTransition.one_of_one_le h]
    exact Ff_one (Submonoid.one_mem _)
  have hfac0 : ∀ k < N, ∀ t, (N : ℝ) * t - k ≤ 0 → fac k t = 1 := fun k hk t h => by
    have hu := hfacU k hk t
    show Ff (σ _, 1, A k) = 1
    rw [show σ (N * t - k) = 0 from Real.smoothTransition.zero_of_nonpos h] at hu ⊢
    exact Ff_zero' hu
  have hfacm : ∀ (k : ℕ) (t : ℝ), g k * fac k t = Ff (σ (N * t - k), g k, g (k + 1)) := fun k t => by
    simp only [fac, Ff, sinv_one, Matrix.one_mul, A]
  let φ : ℝ → Mat n := fun t => ((List.range N).map (fun k => fac k t)).prod
  have hlo : ∀ t m, m ≤ N → (∀ k < m, 1 ≤ (N : ℝ) * t - k) →
      ((List.range m).map (fun k => fac k t)).prod = g m := by
    intro t m
    induction m with
    | zero => intro _ _; simp [hg0]
    | succ m ih =>
      intro hm hk
      rw [List.range_succ, List.map_append, List.prod_append,
        ih (by omega) (fun k hk' => hk k (by omega)), List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, Matrix.mul_one, hfac1 m t (hk m (by omega)), hgA]
  have hhi : ∀ t j m, j < m → m ≤ N → (∀ k, j < k → k < m → (N : ℝ) * t - k ≤ 0) →
      (∀ k < j, 1 ≤ (N : ℝ) * t - k) →
      ((List.range m).map (fun k => fac k t)).prod = g j * fac j t := by
    intro t j m hjm
    induction m with
    | zero => omega
    | succ m ih =>
      intro hm hh hl
      rcases Nat.lt_or_ge j m with h | h
      · rw [List.range_succ, List.map_append, List.prod_append,
          ih h (by omega) (fun k a b => hh k a (by omega)) hl]
        simp [hfac0 m (by omega) t (hh m h (by omega))]
      · obtain rfl : j = m := by omega
        rw [List.range_succ, List.map_append, List.prod_append, hlo t j (by omega) hl]
        simp
  have heval : ∀ j < N, ∀ t, (j : ℝ) ≤ N * t → (N : ℝ) * t ≤ j + 1 →
      φ t = Ff (σ (N * t - j), g j, g (j + 1)) := fun j hj t h1 h2 => by
    rw [← hfacm]
    refine hhi t j N hj le_rfl (fun k a _ => ?_) (fun k a => ?_)
    · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast a
      linarith
    · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast a
      linarith
  have hleft : ∀ t ≤ (0 : ℝ), φ t = 1 := fun t ht => by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have hk' := List.mem_range.1 hk
    exact hfac0 k hk' t (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [hNr])
  have hright : ∀ t, 1 ≤ t → φ t = ψ 1 := fun t ht => by
    rw [← hgN]
    refine hlo t N le_rfl (fun k hk => ?_)
    have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    nlinarith [hNr]
  -- smoothness
  have hφd : ContDiff ℝ 1 φ := contDiff_list_prod fun k hk =>
    contDiffOn_Ff.comp_contDiff
      ((Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub
        contDiff_const)).prodMk contDiff_const)
      (fun t => hfacU k (List.mem_range.1 hk) t)
  have hφD : ∀ t, HasDerivAt φ (deriv φ t) t := fun t =>
    ((hφd.differentiable one_ne_zero) t).hasDerivAt
  have hd0 : deriv φ 0 = 0 := by
    have h1 : HasDerivWithinAt φ 0 (Set.Iic 0) 0 :=
      (hasDerivWithinAt_const 0 (Set.Iic 0) (1 : Mat n)).congr (fun t ht => hleft t ht)
        (hleft 0 le_rfl)
    exact (uniqueDiffWithinAt_Iic 0).eq_deriv _ (hφD 0).hasDerivWithinAt h1
  have hd1 : deriv φ 1 = 0 := by
    have h1 : HasDerivWithinAt φ 0 (Set.Ici 1) 1 :=
      (hasDerivWithinAt_const 1 (Set.Ici 1) (ψ 1)).congr (fun t ht => hright t ht)
        (hright 1 le_rfl)
    exact (uniqueDiffWithinAt_Ici 1).eq_deriv _ (hφD 1).hasDerivWithinAt h1
  have hsymp : ∀ t, IsSymplectic (φ t) := fun t => list_prod_mem fun k hk =>
    Ff_mem (Submonoid.one_mem _) (hA k) (hfacU k (List.mem_range.1 hk) t)
  obtain ⟨H, hHf, hH⟩ := symLoop_of_symplecticPath_family n (fun _ => φ) (fun _ => deriv φ)
    (hφd.continuous.comp continuous_snd) ((hφd.continuous_deriv le_rfl).comp continuous_snd)
    (fun _ t => hφD t) (fun _ t _ => hsymp t) (fun _ => hleft 0 le_rfl) (fun _ => hd0)
    (fun _ => hd1) (fun _ => by rw [hright 1 le_rfl]; exact hψ1)
  let S : ℝ → Mat n := fun t => H (0, t)
  obtain ⟨Ψ, hΨ, -⟩ := fundamentalSolution_existsUnique n S (hH 0).1.1
  refine ⟨S, Ψ, (hH 0).1, (hH 0).2.1, ?_, hΨ, fun t i j => ?_⟩
  · show H (0, 0) = 0
    rw [hHf]; simp [hd0]
  · rw [(hH 0).2.2 Ψ hΨ t t.2]
    obtain ⟨m, hm, h1, h2⟩ := exists_cell hN0 t.2
    rw [heval m hm t h1 h2]
    have hk := hC (κ (⟨σ (N * t - m), hσ _⟩, node m)) ⟨_, rfl⟩ (σ (N * t - m), g m, g (m + 1))
      (by simpa [κ] using hδ₂) (fun i j => by simpa [κ, g] using hδ₂)
      (fun i' j' => (hclose m hm i' j').trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      i j
    have hfk : Ff (κ (⟨σ (N * t - m), hσ _⟩, node m)) = ψ (node m) := Ff_self _ (hψ _)
    rw [hfk] at hk
    have hd : dist (node m) t < η := by
      rw [Subtype.dist_eq, hnode m hm.le, Real.dist_eq]
      have hN1 : (m : ℝ) / N ≤ t := by rw [div_le_iff₀ hNr]; linarith
      have hN2 : (t : ℝ) - m / N ≤ 1 / N := by
        rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hNr]; linarith
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    have hψt := (hψu (node m) t hd i j).trans_le (min_le_right _ _)
    have := abs_sub_le (Ff (σ (N * t - m), g m, g (m + 1)) i j) (ψ (node m) i j) (ψ t i j)
    linarith

end An

end CRJ3C

theorem solution (n : ℕ) (ψ : C(unitInterval, Mat n))
    (hψ : ∀ t, IsSymplectic (ψ t)) (hψ0 : ψ 0 = 1) (hψ1 : (1 - ψ 1).det ≠ 0) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ S Ψ : ℝ → Mat n, IsSymLoop S ∧ IsNondegenerate S ∧ S 0 = 0 ∧
      IsFundamentalSolution S Ψ ∧ ∀ t : unitInterval, ∀ i j, |Ψ t i j - ψ t i j| < ε :=
  CRJ3C.d3 n ψ hψ hψ0 hψ1 ε hε
