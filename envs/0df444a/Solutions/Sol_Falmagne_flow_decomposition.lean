-- Prove2me | solution 1 for Falmagne.flow_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:59.784523+00:00
-- url     : https://prove2.me/submissions/b092c324-a3d7-4a78-99de-3d3af832cc11

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
public import Theorems.Thm_Falmagne_flow_outflow_nonneg
public import Theorems.Thm_Falmagne_flow_zero_of_source_zero
public import Theorems.Thm_Falmagne_mem_edgeSupport
public import Theorems.Thm_Falmagne_flow_subtract_path
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_nil
attribute [local simp] Falmagne.pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil


attribute [local simp] Falmagne.mem_edgeSupport

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}
namespace Falmagne
theorem _root_.solution [Nonempty X] (h : IsFlow q m) :
    ∃ μ : List X →₀ ℝ,
      (∀ l, 0 ≤ μ l) ∧
      (∀ l ∈ μ.support, l.Nodup ∧ l.toFinset = Finset.univ) ∧
      μ.sum (fun _ w => w) = m ∧
      (∀ x A, x ∈ A → μ.sum (fun l w => w * pathFlow l x A) = q x A) := by
  classical
  induction hn : (edgeSupport q).card using Nat.strong_induction_on generalizing q m with
  | h n ih =>
      by_cases hm0 : m = 0
      · subst m
        refine ⟨0, by simp, ?_, by simp, ?_⟩
        · intro l hl
          simp at hl
        · intro x A hx
          simpa using (flow_zero_of_source_zero h A x hx).symm
      · have hmnn : 0 ≤ m := by rw [← h.source]; exact flow_outflow_nonneg h _
        have hm : 0 < m := lt_of_le_of_ne hmnn (Ne.symm hm0)
        obtain ⟨l, δ, hln, hfull, hδ, hr, hlt⟩ := flow_subtract_path h hm
        obtain ⟨μ, hμnn, hμvalid, hμmass, hμedge⟩ :=
          ih _ (by simpa [hn] using hlt) hr rfl
        refine ⟨μ + Finsupp.single l δ, ?_, ?_, ?_, ?_⟩
        · intro k
          simp only [Finsupp.add_apply, Finsupp.single_apply]
          split_ifs <;> linarith [hμnn k]
        · intro k hk
          have hku := Finsupp.support_add hk
          rcases Finset.mem_union.mp hku with hkm | hkl
          · exact hμvalid k hkm
          · have hkl' := (Finsupp.mem_support_single k l δ).mp hkl
            rw [hkl'.1]
            exact ⟨hln, hfull⟩
        · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl, hμmass]
          ring
        · intro x A hx
          rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
            Finsupp.sum_single_index (zero_mul _), hμedge x A hx]
          ring
end Falmagne
