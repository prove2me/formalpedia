-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.sc_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:30:31.615626+00:00
-- url     : https://prove2.me/submissions/1dfa613a-5eb5-4cc3-a37d-7cedd8ad1935

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_scale_jet_variable
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_sc_sub_mem

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
theorem _root_.solution {κ : Type} (m : ℕ) (c : R) {b : Jet R κ m} (hb : b ∈ Ij R κ m) :
    sc m c b - c • b ∈ Ij R κ m ^ 2 := by
  have hb' : b ∈ Submodule.span (Jet R κ m) (Set.range (zz (R := R) (κ := κ) m)) := hb
  clear hb
  induction hb' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [scale_jet_variable, sub_self]
    exact Ideal.zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    have h := Ideal.add_mem _ hx hy
    convert h using 1
    rw [map_add, smul_add]
    abel
  | smul a x hx' hx =>
    have e1 : sc m c (a • x) - c • (a • x) =
        sc m c a * (sc m c x - c • x) + (sc m c a - a) * (c • x) := by
      simp only [smul_eq_mul, map_mul, Algebra.smul_def]
      ring
    rw [e1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) ?_
    rw [pow_two (Ij R κ m)]
    exact Ideal.mul_mem_mul (sc_sub_mem m c a) (Submodule.smul_of_tower_mem _ c hx')
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
