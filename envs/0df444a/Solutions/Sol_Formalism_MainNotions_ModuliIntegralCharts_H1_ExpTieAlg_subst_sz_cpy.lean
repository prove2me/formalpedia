-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.subst_sz_cpy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:32.523733+00:00
-- url     : https://prove2.me/submissions/4cc5ddd8-dace-4327-899c-ecaa33224a94

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_hasSubst0
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_hasSubst_cpy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_hasSubst_sz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
variable {N d : ℕ}
private theorem subst_X_lemma_2 {σ : Type} (g : MvPowerSeries σ S) :
    subst (X : σ → MvPowerSeries σ S) g = g := by
  first
  | (rw [subst_self]; rfl)
  | (rw [← map_algebraMap_eq_subst_X]; simp)
private theorem subst_zero_lemma_3 {σ τ : Type} [Finite σ] (g : MvPowerSeries σ S) :
    subst (fun _ : σ => (0 : MvPowerSeries τ S)) g = C (constantCoeff g) := by
  classical
  have hz : HasSubst (fun _ : σ => (0 : MvPowerSeries τ S)) := hasSubst0 (fun _ => map_zero _)
  ext e
  rw [coeff_subst hz, finsum_eq_single _ 0]
  · by_cases he : e = 0 <;> simp [coeff_C, coeff_one, he]
  · intro n hn
    obtain ⟨s, hs⟩ : ∃ s, n s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    have hp : (n.prod fun _ k => (0 : MvPowerSeries τ S) ^ k) = 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)
    simp [hp]
section Exp
variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
end Exp
section Comp
variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
  (h0 : ∀ j, constantCoeff (φ j) = 0) (w : Fin N → Fin d → S)
  (hlin : ∀ q j, coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ j) = w q j)
  (hhom : ∀ j, subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) (F j) =
    subst (fun r : Fin 1 × Fin N =>
      (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) (φ j))
include h0 hlin hhom
end Comp
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj ExpTieAlg NumberField
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
variable {N d : ℕ}
variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
theorem _root_.solution (b : Fin 2) (g : MvPowerSeries (Fin 1 × Fin N) S) :
    subst (sz (S := S) (N := N)) (subst (cpy (S := S) b) g) = if b = 0 then g else C (constantCoeff g) := by
  classical
  rw [subst_comp_subst_apply (hasSubst_cpy b) hasSubst_sz]
  have hf : (fun r : Fin 1 × Fin N => subst (sz (S := S) (N := N)) (cpy (S := S) b r)) =
      fun r => if b = 0 then (X r : MvPowerSeries (Fin 1 × Fin N) S) else 0 := by
    funext r
    rcases r with ⟨a, i⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    show subst (sz (S := S) (N := N)) (X (b, i)) = _
    first
    | (rw [subst_X hasSubst_sz]; by_cases hb : b = 0 <;> simp [sz, hb])
    | rw [subst_X hasSubst_sz]
  rw [hf]
  by_cases hb : b = 0
  · have hX : (fun r : Fin 1 × Fin N => if b = 0 then (X r : MvPowerSeries (Fin 1 × Fin N) S) else 0) = X := by
      funext r
      simp [hb]
    rw [hX, if_pos hb, subst_X_lemma_2]
  · have hZ : (fun r : Fin 1 × Fin N => if b = 0 then (X r : MvPowerSeries (Fin 1 × Fin N) S) else 0) =
        fun _ => 0 := by
      funext r
      simp [hb]
    rw [hZ, if_neg hb, subst_zero_lemma_3]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
