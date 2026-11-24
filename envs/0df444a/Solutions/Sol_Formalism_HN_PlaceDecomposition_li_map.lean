-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.li_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:22.080683+00:00
-- url     : https://prove2.me/submissions/8e11051c-24f7-487d-9a24-cd3b77c6ae5f

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution {K L : Type*} [Field K] [Field L] (σ : K →+* L) {n m : Type*} [Fintype n]
    [Fintype m] [DecidableEq n] [DecidableEq m] (u : n → m → K) (hu : LinearIndependent K u) :
    LinearIndependent L (fun k i => σ (u k i)) := by
  classical
  let f : (n → K) →ₗ[K] (m → K) :=
    { toFun := fun c => ∑ k, c k • u k
      map_add' := by
        intro a c
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        simp [Finset.smul_sum, smul_smul] }
  have hfinj : Function.Injective f := by
    intro a c hac
    have h0 := (Fintype.linearIndependent_iff.1 hu) (a - c) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 hac)
    funext k
    exact sub_eq_zero.1 (h0 k)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.2 hfinj)
  have hgu : ∀ k, g (u k) = Pi.single k 1 := by
    intro k
    have h1 : f (Pi.single k 1) = u k := by
      show ∑ j, (Pi.single k (1 : K) : n → K) j • u j = u k
      simp [Pi.single_apply]
    rw [← h1]
    exact LinearMap.congr_fun hg _
  have hexp : ∀ k, g (u k) = ∑ i, u k i • g (Pi.single i 1) := by
    intro k
    have hx : u k = ∑ i, u k i • (Pi.single i (1 : K) : m → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul]
  have hid : ∀ k k', ∑ i, σ (u k i) * σ (g (Pi.single i 1) k') = if k' = k then 1 else 0 := by
    intro k k'
    have h0 := congrFun ((hexp k).symm.trans (hgu k)) k'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
    have h1 := congrArg σ h0
    rw [map_sum] at h1
    simp only [map_mul] at h1
    rw [h1, Pi.single_apply]
    split_ifs <;> simp
  rw [Fintype.linearIndependent_iff]
  intro c hc k'
  have hc' : ∀ i, ∑ k, c k * σ (u k i) = 0 := by
    intro i
    have h0 := congrFun hc i
    simpa [Finset.sum_apply] using h0
  calc c k' = ∑ k, c k * (if k' = k then 1 else 0) := by simp
    _ = ∑ k, c k * ∑ i, σ (u k i) * σ (g (Pi.single i 1) k') := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hid k k']
    _ = ∑ i, (∑ k, c k * σ (u k i)) * σ (g (Pi.single i 1) k') := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp [hc']
end Formalism.HN.PlaceDecomposition
