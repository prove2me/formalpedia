-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:31:17.131976+00:00
-- url     : https://prove2.me/submissions/e01402a3-2982-4269-9bd9-93d65dcabda2

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_isOpen_Quad
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_ae_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_inf_abs
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_diagDom
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_betaTau_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_betaTau_sesq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_InCC_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dilF_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_scale_qmp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {A : ℝ}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (hC : FormCoreC) (hAe : AeFromTests) (hFa : FatouParam) (hL : CCLin) (hDC : DilCC) (hA : 0 ≤ A)
    (hRB : RegBound D A) (hRA : RegAverage D A) (hU : Unfold D A) (hJ : JCont D A) (hDB : DilBeta D A)
    {τ₀ : ℝ × ℝ} (hτ₀ : τ₀ ∈ Quad) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (hF : InCC A 5 F) (hF' : InCC A 5 F') :
    betaTau D τ₀ F F' = betaInfTau D τ₀ F F' := by
  classical
  have hDD : DiagDom D A := diagDom hAe hFa hRB hRA hU hJ
  let V := CCs k r Wp Wq hL A 4
  let W : Submodule ℂ V := Submodule.comap V.subtype (CCs k r Wp Wq hL A 5)
  have hs1 := betaTau_sesq hJ hDD hτ₀
  have hs2 := hRB.2.2 τ₀ hτ₀
  have key := hC V W (fun x y => betaTau D τ₀ x.1 y.1) (fun x y => betaInfTau D τ₀ x.1 y.1)
    ⟨fun x x' y => hs1.1 _ _ _ x.2 x'.2 y.2, fun x y y' => hs1.2.1 _ _ _ x.2 y.2 y'.2,
      fun a x y => hs1.2.2.1 a _ _ x.2 y.2, fun a x y => hs1.2.2.2 a _ _ x.2 y.2⟩
    ⟨fun x x' y => hs2.1 _ _ _ x.2 x'.2 y.2, fun x y y' => hs2.2.1 _ _ _ x.2 y.2 y'.2,
      fun a x y => hs2.2.2.1 a _ _ x.2 y.2, fun a x y => hs2.2.2.2 a _ _ x.2 y.2⟩
    ?_ ?_ ?_
  · exact key ⟨F, InCC_mono (by norm_num) hF⟩ hF ⟨F', InCC_mono (by norm_num) hF'⟩ hF'
  · intro x
    show (betaTau D τ₀ x.1 x.1).im = 0 ∧ 0 ≤ (betaTau D τ₀ x.1 x.1).re
    rw [betaTau_self hJ x.2 hτ₀]
    simp
  · intro x
    show (betaTau D τ₀ x.1 x.1).re ≤ (betaInfTau D τ₀ x.1 x.1).re
    rw [betaTau_self hJ x.2 hτ₀, Complex.ofReal_re]
    have h0 : 0 ≤ (betaInfTau D τ₀ x.1 x.1).re := by
      rw [inf_abs hAe hRB hRA hU x.2 τ₀ hτ₀, Complex.ofReal_re]; exact abs_nonneg _
    exact ENNReal.toReal_le_of_le_ofReal h0 (hDD x.1 x.2 τ₀ hτ₀).2
  · intro x hx
    obtain ⟨c5, hc5⟩ : InCC A 5 x.1 := hx
    obtain ⟨C, hCd⟩ := hDC k r Wp Wq A hA
    obtain ⟨C0, U0, hU0, hC0⟩ := hRB.1 τ₀ hτ₀
    have hC0' := hC0 τ₀ (mem_of_mem_nhds hU0)
    let box : Set (ℝ × ℝ) := Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2
    have hbox : box ∈ 𝓝 ((1, 1) : ℝ × ℝ) :=
      prod_mem_nhds (Icc_mem_nhds (by norm_num) (by norm_num)) (Icc_mem_nhds (by norm_num) (by norm_num))
    have hmem : ∀ t, t ∈ box → InCC A 4 (dilF t x.1) := fun t h =>
      InCC_mono (by norm_num) ⟨_, (hCd t h x.1 c5 hc5).1⟩
    let Φ : ℝ × ℝ → V := fun t => if h : t ∈ box then ⟨dilF t x.1, hmem t h⟩ else x
    have hΦ : ∀ t, t ∈ box → (Φ t).1 = dilF t x.1 := fun t h => by simp only [Φ, dif_pos h]
    refine ⟨Φ, fun t => (((t.1 * t.2) ^ kap k r : ℝ) : ℂ) * betaInfTau D (τ₀.1 * t.1, τ₀.2 * t.2) x.1 x.1,
      (1, 1), ?_, ?_, ?_, ?_, ?_⟩
    · apply Subtype.ext
      rw [hΦ _ (mem_of_mem_nhds hbox), dilF_one]
    · simp
    · have h1 : ContinuousAt (fun τ => betaInfTau D τ x.1 x.1) τ₀ :=
        (hRB.2.1 x.1 x.1 x.2 x.2).continuousAt (isOpen_Quad.mem_nhds hτ₀)
      have h2 : ContinuousAt (fun t : ℝ × ℝ => (τ₀.1 * t.1, τ₀.2 * t.2)) (1, 1) := by fun_prop
      have h3 : ContinuousAt (fun t : ℝ × ℝ => betaInfTau D (τ₀.1 * t.1, τ₀.2 * t.2) x.1 x.1) (1, 1) :=
        ContinuousAt.comp_of_eq (g := fun τ => betaInfTau D τ x.1 x.1)
          (f := fun t : ℝ × ℝ => (τ₀.1 * t.1, τ₀.2 * t.2)) (y := τ₀) h1 h2 (by simp)
      have h4 : ContinuousAt (fun t : ℝ × ℝ => (((t.1 * t.2) ^ kap k r : ℝ) : ℂ)) (1, 1) := by fun_prop
      exact h4.mul h3
    · have hb : ∀ᶠ t in 𝓝 ((1, 1) : ℝ × ℝ), ‖(betaInfTau D τ₀ (Φ t - x).1 (Φ t - x).1).re‖ ≤
          C0 * (C * (|t.1 - 1| + |t.2 - 1|) * c5) * (C * (|t.1 - 1| + |t.2 - 1|) * c5) := by
        filter_upwards [hbox] with t ht
        have e : (Φ t - x).1 = dilF t x.1 - x.1 := by
          show (Φ t).1 - x.1 = _
          rw [hΦ t ht]
        rw [e]
        have h := (hCd t ht x.1 c5 hc5).2
        exact (Complex.abs_re_le_norm _).trans (hC0' _ _ _ _ h h)
      refine squeeze_zero_norm' hb ?_
      have hc : Continuous fun t : ℝ × ℝ =>
          C0 * (C * (|t.1 - 1| + |t.2 - 1|) * c5) * (C * (|t.1 - 1| + |t.2 - 1|) * c5) := by fun_prop
      have := hc.tendsto (1, 1)
      simpa using this
    · refine ⟨Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2,
        prod_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)) (Ioo_mem_nhds (by norm_num) (by norm_num)), ?_⟩
      have h1 := ae_eq hAe hRB hRA hU x.2
      rw [ae_restrict_iff' isOpen_Quad.measurableSet] at h1
      have h2 := (scale_qmp (ne_of_gt hτ₀.1) (ne_of_gt hτ₀.2)).ae h1
      rw [ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)]
      filter_upwards [h2] with t ht htU
      have t1 : 0 < t.1 := lt_trans (by norm_num) htU.1.1
      have t2 : 0 < t.2 := lt_trans (by norm_num) htU.2.1
      have htq : t ∈ Quad := ⟨t1, t2⟩
      have htb : t ∈ box := ⟨Set.Ioo_subset_Icc_self htU.1, Set.Ioo_subset_Icc_self htU.2⟩
      have hq : (τ₀.1 * t.1, τ₀.2 * t.2) ∈ Quad := ⟨mul_pos hτ₀.1 t1, mul_pos hτ₀.2 t2⟩
      obtain ⟨-, h3⟩ := ht hq
      show betaTau D τ₀ (Φ t).1 (Φ t).1 = _
      rw [hΦ t htb, betaTau_self hJ (hmem t htb) hτ₀, hDB x.1 x.2 τ₀ hτ₀ t htq, ← h3, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
      push_cast
      ring
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
