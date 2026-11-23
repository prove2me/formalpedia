-- Prove2me | solution 1 for Bl.general_b_fact_second_ter_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:28.191871+00:00
-- url     : https://prove2.me/submissions/fe996fb1-b8af-45fe-aeab-9be6d564ccd5

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1
namespace Bl.general_b_fact_second_ter_form
private lemma aux {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type u_1}
    (C : ℂ → Module.End ℂ V) (χ : ι → ℂ → ℂ) (hχ : Function.Injective χ)
    (p : ι → Submodule ℂ V) (hp : ∀ (i : ι) (v : V), v ∈ p i ↔ ∀ w, C w v = χ i w • v)
    [DecidableEq ι] (t : Finset ι) : ∀ i, i ∉ t → Disjoint (p i) (t.sup p) := by
  induction t using Finset.strongInduction with
  | H t ih =>
  intro i hi
  rcases t.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · simp
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  obtain ⟨w, hw⟩ : ∃ w, χ i w ≠ χ j w := by
    by_contra! h
    exact hij (hχ (funext h))
  have hmem : ∀ k v, v ∈ p k → C w v = χ k w • v := fun k v hv => (hp k v).1 hv w
  have key : ∀ v ∈ t.sup p, C w v - χ j w • v ∈ (t.erase j).sup p := by
    intro v hv
    have hle : t.sup p ≤ Submodule.comap (C w - χ j w • LinearMap.id) ((t.erase j).sup p) := by
      refine Finset.sup_le fun k hk => ?_
      intro x hx
      rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        hmem k x hx, ← sub_smul]
      by_cases hkj : k = j
      · simp [hkj]
      · exact Finset.le_sup (f := p) (Finset.mem_erase.2 ⟨hkj, hk⟩) (Submodule.smul_mem _ _ hx)
    have := hle hv
    rwa [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
  rw [Submodule.disjoint_def]
  intro v hvi hvt
  have h1 : C w v - χ j w • v = (χ i w - χ j w) • v := by rw [hmem i v hvi, sub_smul]
  have h2 : (χ i w - χ j w) • v ∈ p i := Submodule.smul_mem _ _ hvi
  have h3 := key v hvt
  rw [h1] at h3
  have h4 := ih (t.erase j) (Finset.erase_ssubset hj) i (fun h => hi (Finset.mem_of_mem_erase h))
  have h5 : (χ i w - χ j w) • v = 0 := (Submodule.disjoint_def.1 h4) _ h2 h3
  rcases smul_eq_zero.1 h5 with h | h
  · exact absurd (sub_eq_zero.1 h) hw
  · exact h
end Bl.general_b_fact_second_ter_form
end

set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_second_ter_form
namespace Bl.general_b_fact_second_ter_form
theorem _root_.solution :
  ∀ {V : Type} [inst : AddCommGroup.{0} V] [inst_1 : Module.{0, 0} Complex V] {ι : Type u_1}
  (C : Complex → Module.End.{0, 0} Complex V) (χ : ι → Complex → Complex),
  Function.Injective.{u_1 + 1, 1} χ →
    ∀ (p : ι → Submodule.{0, 0} Complex V),
      (∀ (i : ι) (v : V),
          Iff (Membership.mem.{0, 0} (p i) v)
            (∀ (w : Complex), Eq.{1} (DFunLike.coe.{1, 1, 1} (C w) v) (HSMul.hSMul.{0, 0, 0} (χ i w) v))) →
        iSupIndep.{u_1 + 1, 0} p := by
  intro V _ _ ι C χ hχ p hp
  classical
  rw [iSupIndep_iff_supIndep]
  intro s
  rw [Finset.supIndep_iff_disjoint_erase]
  intro i _
  exact aux C χ hχ p hp _ i (Finset.notMem_erase i s)
end Bl.general_b_fact_second_ter_form
