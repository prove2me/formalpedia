-- Prove2me | solution 1 for Bl.SimultaneousEigenvectors.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:35.61563+00:00
-- url     : https://prove2.me/submissions/2aabb7a7-2c2a-4690-9637-1f89df12b62a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1
namespace Bl.SimultaneousEigenvectors
private lemma diagonal_apply_comm {n : ℕ} {X : Type u_1} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : ReciprocityTheory.ChartRestriction.DS.IsGlRep A) (c d : Fin n) (v : X) :
    A c c (A d d v) = A d d (A c c v) := by
  by_cases hcd : c = d
  · subst hcd; rfl
  · have h := hA c c d d
    rw [if_neg hcd, if_neg (Ne.symm hcd), sub_zero] at h
    have h2 := LinearMap.congr_fun h v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h2
    exact sub_eq_zero.mp h2
private lemma exists_simultaneous_eigenvector {n : ℕ} {X : Type u_1} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : ReciprocityTheory.ChartRestriction.DS.IsGlRep A) (s : Finset (Fin n)) :
    ∀ (T : Submodule ℂ X), FiniteDimensional ℂ T → (∀ (c : Fin n) (v : X), v ∈ T → A c c v ∈ T) →
      T ≠ ⊥ → ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro T _ _ hT
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
    exact ⟨w, hw, hw0, 0, fun c hc => absurd hc (Finset.notMem_empty c)⟩
  | insert a s ha ih =>
    intro T hfd hinv hT
    have : Nontrivial T := Submodule.nontrivial_iff_ne_bot.mpr hT
    let f : Module.End ℂ T := (A a a).restrict (fun v hv => hinv a v hv)
    obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue f
    obtain ⟨⟨v, hvT⟩, hv⟩ := hl.exists_hasEigenvector
    have hv1 : A a a v = l • v := by
      have := Module.End.mem_eigenspace_iff.mp hv.1
      exact congrArg Subtype.val this
    have hv0 : v ≠ 0 := by
      intro h0
      apply hv.2
      ext
      exact h0
    let T' : Submodule ℂ X := T ⊓ Module.End.eigenspace (A a a) l
    have hvT' : v ∈ T' := Submodule.mem_inf.mpr ⟨hvT, Module.End.mem_eigenspace_iff.mpr hv1⟩
    have hT' : T' ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨v, hvT', hv0⟩
    have : FiniteDimensional ℂ T' := Submodule.finiteDimensional_of_le (inf_le_left : T' ≤ T)
    have hinv' : ∀ (c : Fin n) (u : X), u ∈ T' → A c c u ∈ T' := by
      intro c u hu
      obtain ⟨huT, huE⟩ := Submodule.mem_inf.mp hu
      have hu1 : A a a u = l • u := Module.End.mem_eigenspace_iff.mp huE
      refine Submodule.mem_inf.mpr ⟨hinv c u huT, Module.End.mem_eigenspace_iff.mpr ?_⟩
      rw [diagonal_apply_comm hA a c u, hu1, map_smul]
    obtain ⟨w, hw, hw0, μ, hμ⟩ := ih T' inferInstance hinv' hT'
    obtain ⟨hwT, hwE⟩ := Submodule.mem_inf.mp hw
    have hw1 : A a a w = l • w := Module.End.mem_eigenspace_iff.mp hwE
    refine ⟨w, hwT, hw0, Function.update μ a l, ?_⟩
    intro c hc
    by_cases hca : c = a
    · subst hca
      rw [Function.update_self]
      exact hw1
    · rw [Function.update_of_ne hca]
      exact hμ c ((Finset.mem_insert.mp hc).resolve_left hca)
end Bl.SimultaneousEigenvectors
end

set_option autoImplicit false
universe u_1
open Bl Bl.SimultaneousEigenvectors
namespace Bl.SimultaneousEigenvectors
theorem _root_.solution :
  ∀ {n : Nat} {X : Type u_1} [inst : NormedAddCommGroup.{u_1} X] [inst_1 : InnerProductSpace.{0, u_1} Complex X]
  {A : Fin n → Fin n → Module.End.{0, u_1} Complex X},
  ReciprocityTheory.ChartRestriction.DS.IsGlRep.{u_1} A →
    ∀ (s : Finset.{0} (Fin n)) (T : Submodule.{0, u_1} Complex X),
      FiniteDimensional.{0, u_1} Complex (Subtype.{u_1 + 1} fun (x : X) ↦ Membership.mem.{u_1, u_1} T x) →
        (∀ (c : Fin n) (v : X),
            Membership.mem.{u_1, u_1} T v →
              Membership.mem.{u_1, u_1} T (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} (A c c) v)) →
          Ne.{u_1 + 1} T Bot.bot.{u_1} →
            Exists.{u_1 + 1} fun (w : X) ↦
              And (Membership.mem.{u_1, u_1} T w)
                (And (Ne.{u_1 + 1} w 0)
                  (Exists.{1} fun (μ : Fin n → Complex) ↦
                    ∀ (c : Fin n),
                      Membership.mem.{0, 0} s c →
                        Eq.{u_1 + 1} (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} (A c c) w)
                          (HSMul.hSMul.{0, u_1, u_1} (μ c) w))) := by
  intro n X _ _ A hA s T hfd hinv hT
  obtain ⟨w, hw, hw0, μ, hμ⟩ := exists_simultaneous_eigenvector hA s T hfd hinv hT
  exact ⟨w, hw, hw0, μ, hμ⟩
end Bl.SimultaneousEigenvectors
