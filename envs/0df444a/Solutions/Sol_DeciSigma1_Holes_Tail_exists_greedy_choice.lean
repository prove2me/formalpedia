-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_greedy_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:53.78053+00:00
-- url     : https://prove2.me/submissions/ad35a29d-4eb1-4092-b044-088cfab96e99

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {ι ρ : Type*} [DecidableEq ι] {U₀ P : Finset ι}
    (hdisj : Disjoint U₀ P) (Ω₀ : ι → ρ) (Adm Good : ι → ρ → Prop)
    (Compat : ι → ρ → ι → ρ → Prop) (hU₀ : ∀ u ∈ U₀, Adm u (Ω₀ u))
    (hAdm : ∀ v ∈ P, ∀ x, Good v x → Adm v x)
    (hsymm : ∀ v ∈ P, ∀ w ∈ P, ∀ x y, Good v x → Good w y → Compat v x w y → Compat w y v x)
    (hstep : ∀ v ∈ P, ∀ (U : Finset ι) (Ω : ι → ρ), v ∉ U → (∀ u ∈ U, Adm u (Ω u)) →
      ∃ x, Good v x ∧ ∀ u ∈ U, Compat v x u (Ω u)) :
    ∃ Ω : ι → ρ, (∀ u ∈ U₀, Ω u = Ω₀ u) ∧ (∀ v ∈ P, Good v (Ω v)) ∧
      ∀ v ∈ P, ∀ u ∈ U₀ ∪ P, u ≠ v → Compat v (Ω v) u (Ω u) := by
  suffices h : ∀ Q ⊆ P, ∃ Ω : ι → ρ, (∀ u ∈ U₀, Ω u = Ω₀ u) ∧ (∀ v ∈ Q, Good v (Ω v)) ∧
      ∀ v ∈ Q, ∀ u ∈ U₀ ∪ Q, u ≠ v → Compat v (Ω v) u (Ω u) from h P subset_rfl
  intro Q
  induction Q using Finset.induction_on with
  | empty => exact fun _ => ⟨Ω₀, fun _ _ => rfl, by simp, by simp⟩
  | insert v Q hvQ ih =>
    intro hsub
    have hvP := hsub (Finset.mem_insert_self v Q)
    have hQP : Q ⊆ P := (Finset.subset_insert v Q).trans hsub
    obtain ⟨Ω, hΩ₀, hgood, hcompat⟩ := ih hQP
    have hvU : v ∉ U₀ ∪ Q := by
      simp [Finset.disjoint_right.mp hdisj hvP, hvQ]
    obtain ⟨x, hx, hxc⟩ := hstep v hvP (U₀ ∪ Q) Ω hvU fun u hu => by
      rcases Finset.mem_union.mp hu with hu | hu
      · rw [hΩ₀ u hu]; exact hU₀ u hu
      · exact hAdm u (hQP hu) _ (hgood u hu)
    have hne : ∀ u ∈ U₀ ∪ Q, u ≠ v := by rintro u hu rfl; exact hvU hu
    have hupd : ∀ u ∈ U₀ ∪ Q, Function.update Ω v x u = Ω u :=
      fun u hu => Function.update_of_ne (hne u hu) _ _
    refine ⟨Function.update Ω v x, fun u hu => ?_, fun w hw => ?_, fun w hw u hu huw => ?_⟩
    · rw [hupd u (Finset.mem_union_left _ hu), hΩ₀ u hu]
    · rcases Finset.mem_insert.mp hw with rfl | hwQ
      · rwa [Function.update_self]
      · rw [hupd w (Finset.mem_union_right _ hwQ)]; exact hgood w hwQ
    have hu' : u = v ∨ u ∈ U₀ ∪ Q := by
      simp only [Finset.mem_union, Finset.mem_insert] at hu ⊢; tauto
    rcases Finset.mem_insert.mp hw with rfl | hwQ
    · rcases hu' with rfl | huU
      · exact absurd rfl huw
      · rw [Function.update_self, hupd u huU]; exact hxc u huU
    · rw [hupd w (Finset.mem_union_right _ hwQ)]
      rcases hu' with rfl | huU
      · rw [Function.update_self]
        exact hsymm _ hvP _ (hQP hwQ) _ _ hx (hgood w hwQ) (hxc w (Finset.mem_union_right _ hwQ))
      · rw [hupd u huU]; exact hcompat w hwQ u huU huw
end DeciSigma1.Holes.Tail
