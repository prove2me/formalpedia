-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.isUnit_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:31:53.930269+00:00
-- url     : https://prove2.me/submissions/3df939c8-4a4e-41d1-9b24-57aee225deab

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BalOf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IsUnitCoeffZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
variable {S : Type} [CommRing S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
theorem _root_.solution {m : ℕ} {P : MvPolynomial (Fin 2 × Fin d) S} (U : (Jet S (Fin 2 × Fin d) m)ˣ)
    (hP : Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)) P = U) : IsUnit (coeff 0 P) := by
  have hker : ∀ a ∈ orig S (Fin 2 × Fin d) ^ (m + 1),
      (constantCoeff : MvPolynomial (Fin 2 × Fin d) S →+* S) a = 0 := by
    intro a ha
    have h1 : orig S (Fin 2 × Fin d) ^ (m + 1) ≤ orig S (Fin 2 × Fin d) :=
      Ideal.pow_le_self (Nat.succ_ne_zero m)
    have h2 : orig S (Fin 2 × Fin d) ≤
        RingHom.ker (constantCoeff : MvPolynomial (Fin 2 × Fin d) S →+* S) := by
      unfold orig
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp
    exact h2 (h1 ha)
  let φ := Ideal.Quotient.lift _ (constantCoeff : MvPolynomial (Fin 2 × Fin d) S →+* S) hker
  have hφP : φ (Ideal.Quotient.mk _ P) = coeff 0 P := Ideal.Quotient.lift_mk _ _ _
  have hu : IsUnit (φ (U : Jet S (Fin 2 × Fin d) m)) := U.isUnit.map φ
  rw [← hP, hφP] at hu
  exact hu
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
