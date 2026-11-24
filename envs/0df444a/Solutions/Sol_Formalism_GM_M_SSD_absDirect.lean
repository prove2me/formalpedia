-- Prove2me | solution 1 for Formalism.GM.M.SSD.absDirect
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:06.440353+00:00
-- url     : https://prove2.me/submissions/3bc44b02-83f3-4400-bde2-b3297d49f869

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_topcoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ ι K ι' : Type} [Field K] [DecidableEq σ] [Fintype ι] (sv : ι → σ)
namespace Formalism.GM.M.SSD
theorem _root_.solution (V : ι' → Submodule K (MvPolynomial σ K)) (a : ι' → ι → ℕ) (ha : Function.Injective a)
    (h1 : ∀ L, ∀ v ∈ V L, ∀ m ∈ v.support, sd sv m ≤ a L)
    (h2 : ∀ L, ∀ v ∈ V L, (∀ m, sd sv m = a L → coeff m v = 0) → v = 0) : iSupIndep V := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s
  refine Finset.strongInduction (p := fun s => ∀ (v : ι' → MvPolynomial σ K), (∀ i ∈ s, v i ∈ V i) →
    ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0) (fun s ih => ?_) s
  intro v hv hsum
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨L, hL, hmax⟩ := s.exists_max_image (fun L => ∑ k, a L k) hne
  have key : v L = 0 := by
    apply h2 L (v L) (hv L hL)
    intro m hm
    have := topcoeff sv a ha (fun L v => v ∈ V L) h1 s v hv L hL hmax m hm
    rw [hsum, coeff_zero] at this
    exact this.symm
  have hrest : ∀ i ∈ s.erase L, v i = 0 :=
    ih (s.erase L) (Finset.erase_ssubset hL) v (fun i hi => hv i (mem_of_mem_erase hi))
      (by rw [← Finset.add_sum_erase s v hL, key, zero_add] at hsum; exact hsum)
  intro i hi
  by_cases hiL : i = L
  · subst hiL; exact key
  · exact hrest i (mem_erase.mpr ⟨hiL, hi⟩)
end Formalism.GM.M.SSD
