-- Prove2me | solution 1 for Formalism.REAL.CharId_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:26.214958+00:00
-- url     : https://prove2.me/submissions/43157a70-b24f-443a-a2b6-181bf03c0d98

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
import Theorems.Thm_Formalism_REAL_CharId_F_gen
import Theorems.Thm_Formalism_REAL_twistedAction_mem_tailSubmodule
import Theorems.Thm_Formalism_REAL_CharId_ker
import Theorems.Thm_Formalism_REAL_CharId_sub_lsh_apply_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℂ) (v : V)
    (hv : IsHW E ν v) :
    ∀ k j : ℕ, n ≤ j + k → ∀ q : ℂ[X],
      (∏ s ∈ univ.filter (fun s : Fin n => j ≤ (s : ℕ)), (X - C (lsh ν s))) ∣ q →
      ∀ y ∈ CharId_F E v j, aeval (CharId_M E) q y = 0 := by
  intro k
  induction k with
  | zero =>
    intro j hj q _ y hy
    exact CharId_ker E hE v j q (fun t ht => absurd t.isLt (by omega)) y hy
  | succ k ih =>
    intro j hj q hq y hy
    refine CharId_ker E hE v j q (fun t ht => ?_) y hy
    have hsub : insert t (univ.filter (fun s : Fin n => t.1 + 1 ≤ (s : ℕ))) ⊆
        univ.filter (fun s : Fin n => j ≤ (s : ℕ)) := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rcases hs with rfl | hs <;> omega
    have htn : t ∉ univ.filter (fun s : Fin n => t.1 + 1 ≤ (s : ℕ)) := by simp
    have hdvd := Finset.prod_dvd_prod_of_subset _ _ (fun s => X - C (lsh ν s)) hsub
    rw [Finset.prod_insert htn] at hdvd
    obtain ⟨w, hw⟩ := hdvd.trans hq
    have hq' : q = ((∏ s ∈ univ.filter (fun s : Fin n => t.1 + 1 ≤ (s : ℕ)), (X - C (lsh ν s))) * w) *
        (X - C (lsh ν t)) := by
      rw [hw]; ring
    rw [hq', map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, CharId_sub_lsh_apply_single E ν v hv t]
    refine ih (t.1 + 1) (by omega) _ (dvd_mul_right _ _) _ ?_
    refine Submodule.sum_mem _ fun a ha => twistedAction_mem_tailSubmodule E v _ a t _ (CharId_F_gen E v _ a ?_)
    have h := (Finset.mem_filter.1 ha).2
    exact h
end Formalism.REAL
