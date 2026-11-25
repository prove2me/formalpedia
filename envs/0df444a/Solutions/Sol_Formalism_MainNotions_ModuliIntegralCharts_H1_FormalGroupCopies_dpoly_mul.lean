-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.dpoly_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:05:11.70481+00:00
-- url     : https://prove2.me/submissions/2ff2ea26-a4ce-420b-b8b2-95d3f52e98a2

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_dmon_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_dpoly_monomial

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
variable {R : Type} [CommRing R] {d n : ℕ}
variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
theorem _root_.solution (S : Finset (Fin n)) (P₁ P₂ : MvPolynomial ι R) (h1 : ∀ l ∈ P₁.vars, cp l ∈ S)
    (h2 : ∀ l ∈ P₂.vars, cp l ∉ S) (A B : PS R n d)
    (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DpolyN F cp u (P₁ * P₂) (A * B) = DpolyN F cp u P₁ A * DpolyN F cp u P₂ B := by
  have e : P₁ * P₂ = ∑ m1 ∈ P₁.support, ∑ m2 ∈ P₂.support,
      MvPolynomial.monomial (m1 + m2) (P₁.coeff m1 * P₂.coeff m2) := by
    conv_lhs => rw [P₁.as_sum, P₂.as_sum]
    rw [Finset.sum_mul_sum]
    simp_rw [MvPolynomial.monomial_mul]
  calc DpolyN F cp u (P₁ * P₂) (A * B) = dpolyHom F cp u (A * B) (P₁ * P₂) := rfl
    _ = ∑ m1 ∈ P₁.support, ∑ m2 ∈ P₂.support,
          C (P₁.coeff m1) * DmonN F cp u m1 A * (C (P₂.coeff m2) * DmonN F cp u m2 B) := by
      rw [e, map_sum]
      refine Finset.sum_congr rfl fun m1 hm1 => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun m2 hm2 => ?_
      have hq1 : ∀ l, m1 l ≠ 0 → cp l ∈ S := fun l hl =>
        h1 l ((MvPolynomial.mem_vars_iff_mem_support l).2 ⟨m1, hm1, Finsupp.mem_support_iff.2 hl⟩)
      have hq2 : ∀ l, m2 l ≠ 0 → cp l ∈ Sᶜ := fun l hl =>
        Finset.mem_compl.2 (h2 l ((MvPolynomial.mem_vars_iff_mem_support l).2 ⟨m2, hm2, Finsupp.mem_support_iff.2 hl⟩))
      show DpolyN F cp u _ (A * B) = _
      rw [dpoly_monomial, dmon_mul F cp u S m1 m2 hq1 hq2 A B hA hB, map_mul]
      ring
    _ = DpolyN F cp u P₁ A * DpolyN F cp u P₂ B := by
      unfold DpolyN
      rw [Finset.sum_mul_sum]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
