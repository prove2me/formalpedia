-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.fold_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:00.563645+00:00
-- url     : https://prove2.me/submissions/2a089b01-db7f-477f-90ca-56f46e0ef8db

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_dofN_mul_right
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_dofN_mul_left
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_it_right
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_it_left
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_fold_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_pderiv_kill


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
theorem _root_.solution (S : Finset (Fin n)) (m₁ m₂ : ι →₀ ℕ) (hm1 : ∀ l, m₁ l ≠ 0 → cp l ∈ S)
    (hm2 : ∀ l, m₂ l ≠ 0 → cp l ∈ Sᶜ) (L : List ι) (A B : PS R n d)
    (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    L.foldr (fun l g => (DofN F (cp l) (u l))^[(m₁ + m₂) l] g) (A * B) =
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m₁ l] g) A *
        L.foldr (fun l g => (DofN F (cp l) (u l))^[m₂ l] g) B := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons]
    rw [ih, Finsupp.add_apply]
    have hA' := fold_mem F cp u S m₁ hm1 L A hA
    have hB' := fold_mem F cp u Sᶜ m₂ hm2 L B hB
    by_cases hl : cp l ∈ S
    · have h2 : m₂ l = 0 := by
        by_contra h
        exact (Finset.mem_compl.1 (hm2 l h)) hl
      rw [h2, add_zero, it_right _ _ (fun X => dofN_mul_right F _ _ X _ (fun j =>
        pderiv_kill (i := (cp l, j)) (V := Vc d Sᶜ)
          (fun hc => (Finset.mem_compl.1 (show cp l ∈ Sᶜ from hc)) hl) hB'))]
      rfl
    · have h1 : m₁ l = 0 := by
        by_contra h
        exact hl (hm1 l h)
      rw [h1, zero_add, it_left _ _ (fun X => dofN_mul_left F _ _ _ X (fun j =>
        pderiv_kill (i := (cp l, j)) (V := Vc d S) (fun hc => hl (show cp l ∈ S from hc)) hA'))]
      rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
