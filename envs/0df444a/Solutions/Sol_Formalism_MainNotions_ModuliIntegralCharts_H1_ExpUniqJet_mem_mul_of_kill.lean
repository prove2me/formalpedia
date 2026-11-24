-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.mem_mul_of_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:30:28.900291+00:00
-- url     : https://prove2.me/submissions/38dcbf74-1457-45c3-b367-cc8c5495b902

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_kill_alt_alt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_sub_kill_mem

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R]
variable {n : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
theorem _root_.solution (m : ℕ) (e : Jet R (Fin 2 × Fin n) m) (h0 : kill m 0 e = 0) (h1 : kill m 1 e = 0) :
    e ∈ Kp m 0 * Kp m 1 := by
  have key : ∀ x ∈ Kp (R := R) (n := n) m 0, x - kill m 1 x ∈ Kp m 0 * Kp m 1 := by
    intro x hx
    have hx' : x ∈ Submodule.span (Jet R (Fin 2 × Fin n) m)
        (Set.range fun j : Fin n => zz (R := R) m ((0 : Fin 2), j)) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [kill_alt_alt, if_neg (by simp), sub_self]
      exact Ideal.zero_mem _
    | zero => simp
    | add y z _ _ hy hz =>
      have h := Ideal.add_mem _ hy hz
      convert h using 1
      rw [map_add]
      abel
    | smul a y hy' hy =>
      have e1 : a • y - kill m 1 (a • y) = y * (a - kill m 1 a) + kill m 1 a * (y - kill m 1 y) := by
        rw [smul_eq_mul, map_mul]
        ring
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_mul hy' (sub_kill_mem m 1 a)) (Ideal.mul_mem_left _ _ hy)
  have he0 : e ∈ Kp m 0 := by simpa [h0] using sub_kill_mem m 0 e
  simpa [h1] using key e he0
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
