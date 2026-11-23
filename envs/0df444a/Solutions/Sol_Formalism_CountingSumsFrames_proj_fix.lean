-- Prove2me | solution 1 for Formalism.CountingSumsFrames.proj_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:49.082479+00:00
-- url     : https://prove2.me/submissions/2632b502-c395-4ca5-b914-422593df475c

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_hwc_le_isoC
import Theorems.Thm_Formalism_CountingSumsFrames_typeProj_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_exists_hw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hSP : S ≤ Pol p r LL) (hS : ∀ c d, ∀ x ∈ S, glAct p LL j c d x ∈ S) (hPS : ∀ x ∈ S, P x ∈ S)
    (hT : ∀ h ∈ S, h ≠ 0 → ∀ μ, h ∈ HWC p LL j univ μ → μ ∈ T) : ∀ x ∈ S, P x = x := by
  have hPP : ∀ x, P (P x) = P x := fun x => LinearMap.congr_fun hP.1 x
  set S0 := S ⊓ LinearMap.ker P with hS0
  have hS0 : ∀ y ∈ S0, y = 0 := by
    intro y hy
    by_contra hy0
    obtain ⟨h, hh, hh0, μ, hμ⟩ := exists_hw LL j S0 (inf_le_left.trans hSP) (fun c d z hz => by
      obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
      refine Submodule.mem_inf.mpr ⟨hS c d z hz1, ?_⟩
      rw [LinearMap.mem_ker] at hz2 ⊢
      rw [typeProj_glAct LL j T P hP c d z, hz2, map_zero]) y hy hy0
    have hT' := hT h (Submodule.mem_inf.mp hh).1 hh0 μ hμ
    have hran : h ∈ LinearMap.range P := by
      rw [hP.2.1]
      exact (le_iSup₂ (f := fun la (_ : la ∈ T) => IsoC p LL j univ la) μ hT') (hwc_le_isoC LL j μ hμ)
    obtain ⟨z, hz⟩ := hran
    have : P h = h := by rw [← hz, hPP]
    have h0 : P h = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hh).2
    exact hh0 (this.symm.trans h0)
  intro x hx
  have := hS0 (x - P x) (Submodule.mem_inf.mpr ⟨S.sub_mem hx (hPS x hx), by
    rw [LinearMap.mem_ker, map_sub, hPP, sub_self]⟩)
  exact (sub_eq_zero.mp this).symm
end Formalism.CountingSumsFrames
