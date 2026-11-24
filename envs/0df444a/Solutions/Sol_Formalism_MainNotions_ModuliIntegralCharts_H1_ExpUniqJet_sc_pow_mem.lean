-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.sc_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:23.989912+00:00
-- url     : https://prove2.me/submissions/f8dd48b0-ad55-4be6-bc65-3ef3fc493b4d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_sc_sub_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_sc_one_mem

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
theorem _root_.solution {κ : Type} (m : ℕ) (c : R) :
    ∀ (k : ℕ) {p : Jet R κ m}, p ∈ Ij R κ m ^ k → sc m c p - c ^ k • p ∈ Ij R κ m ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro p _
    simpa using sc_sub_mem m c p
  | succ k ih =>
    intro p hp
    rw [pow_succ (Ij R κ m) k] at hp
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro a ha b hb
      have hsb : sc m c b ∈ Ij R κ m := by
        have h := Ideal.add_mem _ (sc_sub_mem m c b) hb
        simpa using h
      have e : sc m c (a * b) - c ^ (k + 1) • (a * b) =
          (sc m c a - c ^ k • a) * sc m c b + (c ^ k • a) * (sc m c b - c • b) := by
        simp only [map_mul, Algebra.smul_def, map_pow]
        ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ (Ij R κ m) (k + 1)]
        exact Ideal.mul_mem_mul (ih ha) hsb
      · have h2 := sc_one_mem m c hb
        have h3 : c ^ k • a ∈ Ij R κ m ^ k := Submodule.smul_of_tower_mem _ _ ha
        rw [show k + 1 + 1 = k + 2 by ring, pow_add (Ij R κ m) k 2]
        exact Ideal.mul_mem_mul h3 h2
    · intro x y hx hy
      have h := Ideal.add_mem _ hx hy
      convert h using 1
      rw [map_add, smul_add]
      abel
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
