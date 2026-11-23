-- Prove2me | solution 1 for Formalism.CyclotomicNorms.mem_of_repr_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:54.764622+00:00
-- url     : https://prove2.me/submissions/f05aba3f-a619-4da6-aca8-47be9d2c24c0

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan
import Theorems.Thm_Formalism_CyclotomicNorms_repr_diag_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open Formalism Formalism.CyclotomicNorms
variable {G k V : Type} [Group G] [Field k] [AddCommGroup V] [Module k V] {N : ℕ}
namespace Formalism.CyclotomicNorms
theorem _root_.solution (ρ : Representation k G V) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → G → k) (I : Subgroup G) (he : ∀ i, ∀ y ∈ I, ρ y (e i) = χ i y • e i)
    (hsep : ∀ i j, i ≠ j → ∃ y ∈ I, χ i y ≠ χ j y) (W : Submodule k V)
    (hW : ∀ y ∈ I, ∀ x ∈ W, ρ y x ∈ W) :
    ∀ w ∈ W, ∀ i, e.repr w i ≠ 0 → e i ∈ W := by
  intro w hw i hi
  have key : ∀ s : Finset (Fin N), i ∉ s →
      ∃ u ∈ W, e.repr u i ≠ 0 ∧ ∀ l ∈ s, e.repr u l = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      exact ⟨w, hw, hi, fun l hl => by simp at hl⟩
    · intro j s hjs ih hi'
      have hij : i ≠ j := by
        rintro rfl
        exact hi' (Finset.mem_insert_self _ _)
      have his : i ∉ s := fun h => hi' (Finset.mem_insert_of_mem h)
      obtain ⟨u, huW, hui, hus⟩ := ih his
      obtain ⟨y, hyI, hne⟩ := hsep i j hij
      have hc : ∀ l, e.repr (ρ y u - χ j y • u) l = (χ l y - χ j y) * e.repr u l := by
        intro l
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
          repr_diag_apply ρ e χ y (fun m => he m y hyI) u l, sub_mul]
      refine ⟨ρ y u - χ j y • u, W.sub_mem (hW y hyI u huW) (W.smul_mem _ huW), ?_, ?_⟩
      · rw [hc]
        exact mul_ne_zero (sub_ne_zero.mpr hne) hui
      · intro l hl
        rw [hc]
        rcases Finset.mem_insert.mp hl with rfl | hl
        · rw [sub_self, zero_mul]
        · rw [hus l hl, mul_zero]
  obtain ⟨u, huW, hui, hus⟩ := key (Finset.univ.erase i) (by simp)
  have hu : u = e.repr u i • e i := by
    conv_lhs => rw [← e.sum_repr u]
    exact Finset.sum_eq_single i
      (fun l _ hl => by rw [hus l (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩), zero_smul])
      (fun h => absurd (Finset.mem_univ i) h)
  have h2 : (e.repr u i)⁻¹ • u = e i := by
    calc (e.repr u i)⁻¹ • u = (e.repr u i)⁻¹ • (e.repr u i • e i) := by rw [← hu]
      _ = e i := by rw [smul_smul, inv_mul_cancel₀ hui, one_smul]
  rw [← h2]
  exact W.smul_mem _ huW
end Formalism.CyclotomicNorms
