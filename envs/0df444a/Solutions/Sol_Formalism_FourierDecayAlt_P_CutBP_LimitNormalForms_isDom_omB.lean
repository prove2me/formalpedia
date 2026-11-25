-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.isDom_omB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:11:32.813353+00:00
-- url     : https://prove2.me/submissions/e05cee45-3075-4983-9ffb-92dbababd883

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dmin_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Gf_cont
import Theorems.Thm_Formalism_QuantumDeterminants_dInv
import Theorems.Thm_Formalism_QuantumDeterminants_gInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.FourierDecayAlt.P.CutMP
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
theorem _root_.solution {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Q.IsDom k r Bs.z Bs.z' 0 (Gauge.OmB Bs) := by
  refine ⟨?_, ?_⟩
  · have e : Gauge.OmB Bs = {g | 0 < Gf k r Bs.z Bs.z' g} ∩
        ⋂ a : Fin r, {g | Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
      ext g; simp [Gauge.OmB]
    rw [e]
    exact (isOpen_lt continuous_const (BetaSesquilinearity.Gf_cont _ _)).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (BetaSesquilinearity.Dmin_cont _ _ _) continuous_const)
  · rintro g ⟨-, hg⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Sset k r Bs.z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Sset k r Bs.z' := ⟨h', hh', m', hm'.1, rfl⟩
    refine ⟨?_, fun a => ?_⟩
    · rw [gInv k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem _ hs _ hs' g]; exact hg.1
    · rw [dInv k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem _ hs _ hs' g]; exact hg.2 a
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
