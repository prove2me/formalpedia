-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.fourier_transform_identity_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:28.279085+00:00
-- url     : https://prove2.me/submissions/2b93a7dd-fa4b-4b78-b24d-0281fb32a418

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_neg_right
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_ind_of_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_ind_of_not_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_gen_apply
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_model_moves_hold
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_comm
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_Xi_of_eq_sum
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsXi_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
namespace Formalism.L2.PairingIndexBounds.Mv
theorem _root_.solution : Fourier := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ A₂ B₀ B₂ θ Xi hXi h20 hB₀ hB₂ hA SA SB hSA hSB hcard Φ hsupp hinv
  have hreps0 : IsRepsG A₀ A₂ ({0} : Finset A) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]; exact A₂.zero_mem
    · intro x hx y hy _
      rw [Finset.mem_singleton] at hx hy
      rw [hx, hy]
    · intro y hy
      exact ⟨0, Finset.mem_singleton_self 0, by rw [sub_zero]; exact h20 hy⟩
  have hM : ∑ b ∈ SB, gen c A₀ 0 b = (SB.card : k) • ind (A₂ : Set A) := by
    have := model_moves_hold k A B c hc A₀ A₂ B₀ B₂ hB₀ (fun b hb a ha => (hB₂ b).mp hb a ha) hA {0} SB hreps0 hSB
    rwa [Finset.sum_singleton] at this
  have hexp : Φ = ∑ i ∈ SA ×ˢ SB, (Φ i.1 * (SB.card : k)⁻¹) • gen c A₀ (-i.1) i.2 := by
    funext u
    rw [Finset.sum_product, Finset.sum_apply]
    have hin : ∀ t : A, (∑ b ∈ SB, (Φ t * (SB.card : k)⁻¹) • gen c A₀ (-t) b) u = Φ t * ind (A₂ : Set A) (u - t) := by
      intro t
      have h1 := congrFun hM (u - t)
      rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [← Finset.smul_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      have h2 : ∑ b ∈ SB, gen c A₀ (-t) b u = ∑ b ∈ SB, gen c A₀ 0 b (u - t) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gen_apply, gen_apply, add_zero, sub_eq_add_neg]
      rw [h2, h1, mul_assoc, ← mul_assoc _ (SB.card : k), inv_mul_cancel₀ hcard, one_mul]
    rw [Finset.sum_congr rfl (fun t _ => hin t)]
    by_cases hu : u ∈ A₀
    · obtain ⟨x, hxS, hx⟩ := hSA.2.2 u hu
      rw [Finset.sum_eq_single x]
      · rw [ind_of_mem (show u - x ∈ (A₂ : Set A) from hx), mul_one]
        have := hinv x (u - x) hx
        rwa [add_sub_cancel] at this
      · intro t htS htx
        have : u - t ∉ (A₂ : Set A) := by
          intro h
          apply htx
          apply hSA.2.1 t htS x hxS
          have := A₂.sub_mem hx h
          have e : u - x - (u - t) = t - x := by abel
          rwa [e] at this
        rw [ind_of_not_mem this, mul_zero]
      · intro h; exact absurd hxS h
    · rw [hsupp u hu]
      symm
      apply Finset.sum_eq_zero
      intro t ht
      have : u - t ∉ (A₂ : Set A) := by
        intro h
        apply hu
        have := A₀.add_mem (h20 h) (hSA.1 t ht)
        rwa [sub_add_cancel] at this
      rw [ind_of_not_mem this, mul_zero]
  obtain ⟨h, hval⟩ := Xi_of_eq_sum hXi (SA ×ˢ SB) (fun i => Φ i.1 * (SB.card : k)⁻¹) (fun i => -i.1) Prod.snd _ hexp
  refine ⟨h, ?_⟩
  rw [hval, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hW.comm, hXi.fixed hc hW (-t) (A₀.neg_mem (hSA.1 t ht)), hc.map_neg_right, smul_smul]
  congr 1
  ring
end Formalism.L2.PairingIndexBounds.Mv
