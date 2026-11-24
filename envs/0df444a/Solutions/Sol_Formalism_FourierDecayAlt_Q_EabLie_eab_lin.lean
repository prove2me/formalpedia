-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.eab_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:02:51.640625+00:00
-- url     : https://prove2.me/submissions/5c1dad76-8ca4-4d4f-ad48-2c4e3c30671c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_EabPresMain
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hpart_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_rdV_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.EabLie
theorem _root_.solution (i : Fin (r + 1)) (D : Set (Mx k r)) (p q : Fin (mdim k r i))
    (f f₂ : Mx k r → E) (s : ℂ) (hf : SmoothLev k r i D f) (hf₂ : SmoothLev k r i D f₂)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    EH k r (posL k r i p) (posL k r i q) (fun x => f x + s • f₂ x) g =
      EH k r (posL k r i p) (posL k r i q) f g + s • EH k r (posL k r i p) (posL k r i q) f₂ g := by
  have hX1 := (hpart_mem i p q).1
  have hX2 := (hpart_mem i p q).2
  obtain ⟨U1, F1, hU1, hgU1, hF1, hfF1⟩ := hf g hg
  obtain ⟨U2, F2, hU2, hgU2, hF2, hfF2⟩ := hf₂ g hg
  have hU : IsOpen (U1 ∩ U2) := hU1.inter hU2
  have hgU : g ∈ U1 ∩ U2 := ⟨hgU1, hgU2⟩
  have hF1' : ContDiffOn ℝ ∞ F1 (U1 ∩ U2) := hF1.mono Set.inter_subset_left
  have hF2' : ContDiffOn ℝ ∞ F2 (U1 ∩ U2) := hF2.mono Set.inter_subset_right
  have hFs : ContDiffOn ℝ ∞ (fun x => F1 x + s • F2 x) (U1 ∩ U2) := hF1'.add (hF2'.const_smul s)
  have hfs : ∀ x ∈ U1 ∩ U2, x ∈ Glev k r i → f x + s • f₂ x = F1 x + s • F2 x :=
    fun x hx hxG => by rw [hfF1 x hx.1 hxG, hfF2 x hx.2 hxG]
  have hd1 : DifferentiableAt ℝ F1 g :=
    (hF1.differentiableOn (by simp)).differentiableAt (hU1.mem_nhds hgU1)
  have hd2 : DifferentiableAt ℝ F2 g :=
    (hF2.differentiableOn (by simp)).differentiableAt (hU2.mem_nhds hgU2)
  have key : ∀ X : Mx k r, (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) →
      RdV X (fun x => f x + s • f₂ x) g = RdV X f g + s • RdV X f₂ g := by
    intro X hX
    have hfd : fderiv ℝ (fun x => F1 x + s • F2 x) g = fderiv ℝ F1 g + s • fderiv ℝ F2 g :=
      (hd1.hasFDerivAt.add (hd2.hasFDerivAt.const_smul s)).fderiv
    rw [rdV_ext i X hX (fun x => f x + s • f₂ x) (fun x => F1 x + s • F2 x) (U1 ∩ U2) g hU hgU hg.1 hFs hfs,
      rdV_ext i X hX f F1 U1 g hU1 hgU1 hg.1 hF1 hfF1, rdV_ext i X hX f₂ F2 U2 g hU2 hgU2 hg.1 hF2 hfF2, hfd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp only [EH, EabH]
  rw [key _ hX1, key _ hX2]
  simp only [smul_add]
  rw [smul_comm Complex.I s]
  abel
end Formalism.FourierDecayAlt.Q.EabLie
