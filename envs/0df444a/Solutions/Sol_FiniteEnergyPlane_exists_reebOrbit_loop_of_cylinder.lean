-- Prove2me | solution 1 for FiniteEnergyPlane.exists_reebOrbit_loop_of_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T17:17:49.041958+00:00
-- url     : https://prove2.me/submissions/91f538e0-b881-43e4-a972-a188482f2864

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_loopAction_le_and_dlambdaEnergy_annulus_eq
import Theorems.Thm_FiniteEnergyPlane_ofReal_loopAction_ccwLoop_le_energy
import Theorems.Thm_FiniteEnergyPlane_tendsto_loopAction_of_isRemovablePuncture
import Theorems.Thm_FiniteEnergyPlane_loopAction_cwLoop_eq_neg_ccwLoop
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_punctured_disk_asymptotics
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_inv_exterior
import Theorems.Thm_FiniteEnergyPlane_eq_trivialCylinder_of_dlambdaEnergy_eq_zero
import Theorems.Thm_FiniteEnergyPlane_trivialCylinder_loop_spec



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Restriction of a finite-energy curve to a smaller set. -/
theorem sac_isFiniteEnergyCurve_mono {n : ℕ} (H : V n → ℝ) (J : V n → V n →L[ℝ] V n)
    {U U' : Set ℂ} (hsub : U' ⊆ U) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) :
    IsFiniteEnergyCurve H J U' u := by
  refine ⟨hu.1.mono hsub, fun z hz => hu.2.1 z (hsub hz), fun z hz => hu.2.2.1 z (hsub hz), ?_⟩
  refine lt_of_le_of_lt ?_ hu.2.2.2
  exact iSup₂_mono fun φ _ => lintegral_mono_set hsub

/-- A finite-energy cylinder with `dλ`-energy below every gap of the action spectrum and with
actions bounded below on all counterclockwise circles has a unit circle loop which is a periodic
orbit of period at most `C`. -/
theorem exists_reebOrbit_loop_of_cylinder_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (w : ℂ → V n)
    (hw : IsFiniteEnergyCurve H J {z | z ≠ 0} w) (C e η : ℝ) (he : 0 < e)
    (he₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ C → Q₂.T ≤ C → Q₁.T ≠ Q₂.T → e < |Q₁.T - Q₂.T|)
    (hη : 0 < η) (hE : energy H {z | z ≠ 0} w ≤ ENNReal.ofReal C)
    (hd : dlambdaEnergy H {z | z ≠ 0} w ≤ ENNReal.ofReal e)
    (hact : ∀ ρ : ℝ, 0 < ρ → η ≤ loopAction H w (ccwLoop ρ)) :
    ∃ Q : ReebOrbit H, Q.T ≤ C ∧ ∃ c : ℝ, ∀ t : ℝ,
      loopInS H w (ccwLoop 1) t = Q.x (Q.T * t + c) := by
  classical
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set Uz : Set ℂ := {z | z ≠ 0} with hUz
  have hUzo : IsOpen Uz := isOpen_ne
  set L : ℝ → ℝ := fun ρ => loopAction H w (ccwLoop ρ) with hL
  have hpw : ContDiffOn ℝ ∞ (fun z => proj H (w z)) Uz :=
    hprojs.comp hw.1 (fun z hz => hw.2.1 z hz)
  have hcirc : ∀ ρ : ℝ, 0 < ρ → ∀ θ, circleMap 0 ρ θ ∈ Uz := by
    intro ρ h0 θ
    have hn : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos h0]
    exact norm_pos_iff.1 (by rw [hn]; exact h0)
  -- clockwise and counterclockwise actions
  have hcw : ∀ ρ : ℝ, 0 < ρ → loopAction H w (cwLoop 0 ρ) = -L ρ := by
    intro ρ h0
    exact loopAction_cwLoop_eq_neg_ccwLoop H w hUzo hpw ρ (hcirc ρ h0)
  -- Stokes
  have hSt : ∀ a b : ℝ, 0 < a → a ≤ b → L a ≤ L b ∧
      dlambdaEnergy H (ball 0 b \ ball 0 a) w = ENNReal.ofReal (L b - L a) := by
    intro a b ha hab
    exact loopAction_le_and_dlambdaEnergy_annulus_eq H hH J hJ Uz hUzo w hw a b ha hab fun z h1 _ =>
      norm_pos_iff.1 (lt_of_lt_of_le ha h1)
  have hLe : ∀ a b : ℝ, 0 < a → a ≤ b → L b - L a ≤ e := by
    intro a b ha hab
    have h1 := (hSt a b ha hab).2
    have h2 : dlambdaEnergy H (ball 0 b \ ball 0 a) w ≤ ENNReal.ofReal e :=
      (lintegral_mono_set fun z hz => norm_pos_iff.1
        (lt_of_lt_of_le ha (by simpa using hz.2))).trans hd
    rw [h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff he.le).1 h2
  -- the puncture at `0`
  have hw0 : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) w :=
    sac_isFiniteEnergyCurve_mono H J (fun z hz => hz.2) w hw
  have hρs : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hρp : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hposev : ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0 < ρ := self_mem_nhdsWithin
  rcases punctured_disk_asymptotics H hH J hJ w hw0 with hrem | ⟨Q₀, -, hQ₀, -, hneg, hl₀⟩
  · exfalso
    have h0 := tendsto_loopAction_of_isRemovablePuncture H hH J hJ w hrem
    have h1 : ∀ᶠ ρ : ℝ in 𝓝[>] 0, loopAction H w (cwLoop 0 ρ) ≤ -η :=
      hposev.mono fun ρ hρ => by
        rw [hcw ρ hρ]; exact neg_le_neg (hact ρ hρ)
    have := le_of_tendsto h0 h1
    linarith
  have hQ₀le : Q₀ ≤ -η := le_of_tendsto hQ₀ (hposev.mono fun ρ hρ => by
    rw [hcw ρ hρ]; exact neg_le_neg (hact ρ hρ))
  have hQ₀neg : Q₀ < 0 := by linarith
  have hnegw := hneg hQ₀neg
  obtain ⟨-, -, P₀, hP₀, -⟩ := hl₀ _ hρp hρs
  have hL0 : Tendsto L (𝓝[>] 0) (𝓝 (-Q₀)) := by
    refine hQ₀.neg.congr' (hposev.mono fun ρ hρ => ?_)
    rw [hcw ρ hρ, neg_neg]
  -- the puncture at `∞`
  set w' : ℂ → V n := fun z => w z⁻¹ with hw'def
  have hwe : IsFiniteEnergyCurve H J {z | 1 < ‖z‖} w :=
    sac_isFiniteEnergyCurve_mono H J (fun z hz => norm_pos_iff.1 (lt_trans one_pos hz)) w hw
  have hw'fe : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) w' :=
    (isFiniteEnergyCurve_comp_inv_exterior H hH J hJ 1 1 one_pos (by norm_num) w hwe).1
  have hinv : ∀ ρ t : ℝ, 0 < ρ → (cwLoop 0 ρ t)⁻¹ = ccwLoop ρ⁻¹ t := by
    intro ρ t h0
    simp only [cwLoop, ccwLoop, zero_add, mul_inv, ← Complex.exp_neg, Complex.ofReal_inv]
    congr 2
    ring
  have hcw' : ∀ ρ : ℝ, 0 < ρ → loopAction H w' (cwLoop 0 ρ) = L ρ⁻¹ := by
    intro ρ h0
    have hl : loopInS H w' (cwLoop 0 ρ) = loopInS H w (ccwLoop ρ⁻¹) := by
      funext t
      simp only [loopInS, hw'def, hinv ρ t h0]
    simp only [loopAction, hl, hL]
  rcases punctured_disk_asymptotics H hH J hJ w' hw'fe with hrem | ⟨Q₁, -, hQ₁, -, -, hl₁⟩
  · exfalso
    have h0 := tendsto_loopAction_of_isRemovablePuncture H hH J hJ w' hrem
    have h1 : ∀ᶠ ρ : ℝ in 𝓝[>] 0, η ≤ loopAction H w' (cwLoop 0 ρ) :=
      hposev.mono fun ρ hρ => by
        rw [hcw' ρ hρ]; exact hact _ (inv_pos.2 hρ)
    have := ge_of_tendsto h0 h1
    linarith
  have hQ₁ge : η ≤ Q₁ := ge_of_tendsto hQ₁ (hposev.mono fun ρ hρ => by
    rw [hcw' ρ hρ]; exact hact _ (inv_pos.2 hρ))
  have hQ₁pos : 0 < Q₁ := by linarith
  obtain ⟨-, -, P₁, hP₁, -⟩ := hl₁ _ hρp hρs
  have hLinf : Tendsto (fun ρ : ℝ => L ρ⁻¹) (𝓝[>] 0) (𝓝 Q₁) :=
    hQ₁.congr' (hposev.mono fun ρ hρ => hcw' ρ hρ)
  -- bounds on the actions
  have hLC : ∀ ρ : ℝ, 0 < ρ → L ρ ≤ C := by
    intro ρ hρ
    have h1 := (ofReal_loopAction_ccwLoop_le_energy H hH J hJ w hw hnegw ρ hρ).trans hE
    rcases ENNReal.ofReal_le_ofReal_iff'.1 h1 with h | h
    · exact h
    · have := hact ρ hρ
      simp only [hL] at *
      linarith
  have hQ₁C : Q₁ ≤ C := le_of_tendsto hLinf (hposev.mono fun ρ hρ => hLC _ (inv_pos.2 hρ))
  -- `-Q₀ ≤ L ρ ≤ Q₁`
  have hsmall : ∀ᶠ ρ' : ℝ in 𝓝[>] (0 : ℝ), ∀ ρ₀ : ℝ, 0 < ρ₀ → ρ' < ρ₀ → 0 < ρ' := by
    exact hposev.mono fun ρ' h _ _ _ => h
  have hL_ge : ∀ ρ : ℝ, 0 < ρ → -Q₀ ≤ L ρ := by
    intro ρ hρ
    refine le_of_tendsto hL0 ?_
    filter_upwards [Ioo_mem_nhdsGT hρ] with ρ' hρ'
    exact (hSt ρ' ρ hρ'.1 hρ'.2.le).1
  have hL_le : ∀ ρ : ℝ, 0 < ρ → L ρ ≤ Q₁ := by
    intro ρ hρ
    refine ge_of_tendsto hLinf ?_
    filter_upwards [Ioo_mem_nhdsGT (inv_pos.2 hρ)] with ρ' hρ'
    refine (hSt ρ ρ'⁻¹ hρ ?_).1
    rw [le_inv_comm₀ hρ hρ'.1]
    exact hρ'.2.le
  have hgap : Q₁ - (-Q₀) ≤ e := by
    have hlim := hLinf.sub hL0
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ρ' hρ'
    refine hLe ρ' ρ'⁻¹ hρ'.1 ?_
    have h1 : 1 ≤ ρ'⁻¹ := (one_le_inv₀ hρ'.1).2 hρ'.2.le
    linarith [hρ'.2]
  have hP₀T : P₀.T = -Q₀ := by rw [hP₀, abs_of_neg hQ₀neg]
  have hP₁T : P₁.T = Q₁ := by rw [hP₁, abs_of_pos hQ₁pos]
  have hQ₀₁ : -Q₀ ≤ Q₁ := (hL_ge 1 one_pos).trans (hL_le 1 one_pos)
  have heq : Q₁ = -Q₀ := by
    by_contra hne
    have h1 := he₂ P₁ P₀ (by rw [hP₁T]; exact hQ₁C) (by rw [hP₀T]; linarith)
      (by rw [hP₁T, hP₀T]; exact hne)
    rw [hP₁T, hP₀T, abs_of_nonneg (by linarith)] at h1
    linarith
  have hLconst : ∀ ρ : ℝ, 0 < ρ → L ρ = Q₁ := fun ρ hρ =>
    le_antisymm (hL_le ρ hρ) (by rw [heq]; exact hL_ge ρ hρ)
  -- zero `dλ`-energy
  have hD0 : dlambdaEnergy H Uz w = 0 := by
    set μw := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (dlambdaDensity H w z))
    have hμw : ∀ s : Set ℂ, MeasurableSet s → dlambdaEnergy H s w = μw s := fun s hs =>
      (withDensity_apply _ hs).symm
    have hUeq : Uz = ⋃ N : ℕ, ball (0 : ℂ) ((N : ℝ) + 1) \ ball 0 ((N : ℝ) + 1)⁻¹ := by
      ext z
      simp only [hUz, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_diff, mem_ball_zero_iff, not_lt]
      constructor
      · intro hz
        have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
        obtain ⟨N, hN⟩ := exists_nat_gt (max ‖z‖ ‖z‖⁻¹)
        refine ⟨N, by linarith [le_max_left ‖z‖ ‖z‖⁻¹], ?_⟩
        rw [inv_le_comm₀ (by positivity) hzp]
        linarith [le_max_right ‖z‖ ‖z‖⁻¹]
      · rintro ⟨N, -, hN⟩
        exact norm_pos_iff.1 (lt_of_lt_of_le (by positivity) hN)
    rw [hμw _ hUzo.measurableSet, hUeq]
    refine measure_iUnion_null fun N => ?_
    rw [← hμw _ (measurableSet_ball.diff measurableSet_ball)]
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hle : ((N : ℝ) + 1)⁻¹ ≤ (N : ℝ) + 1 := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) N
        linarith
      exact (inv_le_one_of_one_le₀ h1).trans h1
    rw [(hSt _ _ (inv_pos.2 hN1) hle).2, hLconst _ hN1, hLconst _ (inv_pos.2 hN1), sub_self,
      ENNReal.ofReal_zero]
  -- nonconstant
  have hγ1 : ∀ t : ℝ, ccwLoop 1 t ≠ 0 := by
    intro t
    simp [ccwLoop, Complex.exp_ne_zero]
  have hL1 : 0 < L 1 := lt_of_lt_of_le hη (hact 1 one_pos)
  have hnc : ∃ z₁ : ℂ, z₁ ≠ 0 ∧ ∃ z₂ : ℂ, z₂ ≠ 0 ∧ w z₁ ≠ w z₂ := by
    by_contra hcon
    push_neg at hcon
    have hconst : loopInS H w (ccwLoop 1) = fun _ => loopInS H w (ccwLoop 1) 0 := by
      funext t
      simp only [loopInS]
      rw [hcon _ (hγ1 t) _ (hγ1 0)]
    have h0 : L 1 = 0 := by
      simp only [hL, loopAction]
      rw [hconst]
      simp [liouville, omega0, dot]
    linarith
  -- classification
  obtain ⟨P, k, -, c0, hc0, hwP⟩ :=
    eq_trivialCylinder_of_dlambdaEnergy_eq_zero H hH J hJ w hw hnc hD0
  obtain ⟨-, c', hloop, hactP⟩ := trivialCylinder_loop_spec H hH P k c0 hc0
  have hloopeq : loopInS H w (ccwLoop 1) =
      loopInS H (fun z => trivialCylinder P (c0 * z ^ k)) (ccwLoop 1) := by
    funext t
    simp only [loopInS]
    rw [hwP _ (hγ1 t)]
  have hkT : (k : ℝ) * P.T = L 1 := by
    rw [← hactP]
    simp only [hL, loopAction]
    rw [hloopeq]
  have hkpos : (0 : ℝ) < k := by
    by_contra hle
    push_neg at hle
    nlinarith [P.T_pos]
  let P' : ReebOrbit H :=
    { x := P.x
      T := k * P.T
      T_pos := mul_pos hkpos P.T_pos
      mem := P.mem
      hasDerivAt := P.hasDerivAt
      periodic := fun τ => (Function.Periodic.int_mul (fun τ => P.periodic τ) k) τ }
  refine ⟨P', ?_, c', fun t => ?_⟩
  · show (k : ℝ) * P.T ≤ C
    rw [hkT]
    exact hLC 1 one_pos
  · rw [hloopeq]
    exact hloop t

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (w : ℂ → V n)
    (hw : IsFiniteEnergyCurve H J {z | z ≠ 0} w) (C e η : ℝ) (he : 0 < e)
    (he₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ C → Q₂.T ≤ C → Q₁.T ≠ Q₂.T → e < |Q₁.T - Q₂.T|)
    (hη : 0 < η) (hE : energy H {z | z ≠ 0} w ≤ ENNReal.ofReal C)
    (hd : dlambdaEnergy H {z | z ≠ 0} w ≤ ENNReal.ofReal e)
    (hact : ∀ ρ : ℝ, 0 < ρ → η ≤ loopAction H w (ccwLoop ρ)) :
    ∃ Q : ReebOrbit H, Q.T ≤ C ∧ ∃ c : ℝ, ∀ t : ℝ,
      loopInS H w (ccwLoop 1) t = Q.x (Q.T * t + c) :=
  exists_reebOrbit_loop_of_cylinder_aux H hH J hJ w hw C e η he he₂ hη hE hd hact
