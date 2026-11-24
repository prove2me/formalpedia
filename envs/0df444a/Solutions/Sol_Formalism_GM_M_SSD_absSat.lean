-- Prove2me | solution 1 for Formalism.GM.M.SSD.absSat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:06.755879+00:00
-- url     : https://prove2.me/submissions/79bd5f8a-1dd1-43f7-8b1c-5bd3126f0a1a

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
    (C : AddSubgroup K) (T : AddSubgroup (MvPolynomial σ K))
    (h1 : ∀ L, ∀ v ∈ V L, ∀ m ∈ v.support, sd sv m ≤ a L)
    (hT : ∀ f ∈ T, ∀ m, coeff m f ∈ C)
    (h2 : ∀ L, ∀ v ∈ V L, (∀ m, sd sv m = a L → coeff m v ∈ C) → v ∈ T)
    (s : Finset ι') (v : ι' → MvPolynomial σ K) (hv : ∀ L ∈ s, v L ∈ V L)
    (hC : ∀ m, coeff m (∑ L ∈ s, v L) ∈ C) : ∑ L ∈ s, v L ∈ T := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨L, hL, hmax⟩ := s.exists_max_image (fun L => ∑ k, a L k) hne
  have key : v L ∈ T := by
    apply h2 L (v L) (hv L hL)
    intro m hm
    rw [← topcoeff sv a ha (fun L v => v ∈ V L) h1 s v hv L hL hmax m hm]
    exact hC m
  have hsplit := Finset.add_sum_erase s v hL
  have hrest : ∑ i ∈ s.erase L, v i ∈ T := by
    apply ih (s.erase L) (Finset.erase_ssubset hL) (fun i hi => hv i (mem_of_mem_erase hi))
    intro m
    have : ∑ i ∈ s.erase L, v i = ∑ i ∈ s, v i - v L := by rw [← hsplit]; ring
    rw [this, coeff_sub]
    exact C.sub_mem (hC m) (hT _ key m)
  rw [← hsplit]
  exact T.add_mem key hrest
end Formalism.GM.M.SSD
