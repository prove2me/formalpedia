-- Prove2me | solution 1 for CompanionTheory.D.DSIC.dsInfCharCap_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:53.147311+00:00
-- url     : https://prove2.me/submissions/e81a4309-2fc4-4bc7-ab4e-08ffa03a97d5

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CobApplyOfDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.DSIC
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsWtOn inG inK IsKStableOn)
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.DSIC
theorem _root_.solution (hC : AlgCoreSub) (hM : SmMod) (hQ : ActQ) (hSp : Spread) (hKS : KFinSm) (hKF : KFinStab)
    (hSL : StabLink) (hH : HWofType) (hT : TypeOfHW) : PI.DSInfCharCap.DSInfCharCap := by
  intro n ε lam H _ _ σ hlam ⟨hc, _, hU, hI, _, ⟨T, hTt⟩, hmin⟩ v hv Y
  obtain ⟨S, E, hS⟩ := hM n ε H σ hU
  have hTS : T ≤ S := fun x hx => (hS.mem x).2 (hKS n ε H σ hU hI x ⟨T, hTt.1, hx, hTt.2.1⟩)
  obtain ⟨v₀, h0, hv₀T, hv₀⟩ := hH n ε H σ S E hU hS _ T hTt hTS
  obtain ⟨V₀, hV₀, hV₀s⟩ := hKF n ε H σ S E hU hS
  have := hTt.1
  have hfd : FiniteDimensional ℂ (T.comap S.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hTS).symm.finiteDimensional
  have hmap : (T.comap S.subtype).map S.subtype = T := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hTS]
  have hst : KStab ε E (T.comap S.subtype) := (hSL n ε H σ S E hU hS _ hfd).2 (by rw [hmap]; exact hTt.2.1)
  have hcore := hC n ε lam S E V₀ v₀ (T.comap S.subtype) hlam hS.gl hS.unit hV₀s
    (fun x hx => (hV₀ x).2 ⟨T, hTt.1, hx, hTt.2.1⟩) hv₀ hfd hst hv₀T
    (fun μ x hx hx0 hxh => by
      obtain ⟨T', hT'⟩ := hT n ε H σ S E hU hS μ x hx0 ((hV₀ x).1 hx) hxh
      exact hmin μ T' hT')
  have h := hSp n ε lam H σ S E hU hI hS v₀ h0 hcore ⟨v, (hS.mem v).2 hv⟩ Y
  have hq := hQ n ε H σ S E hS (Y + ((n : ℂ) - 1) / 2) ⟨v, (hS.mem v).2 hv⟩
  rw [h] at hq
  exact hq
end CompanionTheory.D.DSIC
