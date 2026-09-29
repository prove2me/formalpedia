-- Prove2me | solution 1 for BraidsLinksMCG.configProj_isCoveringMap
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:54:59.315984+00:00
-- url     : https://prove2.me/submissions/5be6d908-554a-4774-b4bb-09c8a41323d9

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace CovSol

/-- Relabelling action of the symmetric group on ordered configurations. -/
instance permAction (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (OrderedConfig n) where
  smul g p := ⟨p.1 ∘ ⇑g⁻¹, p.2.comp (g⁻¹).injective⟩
  one_smul p := by apply Subtype.ext; funext i; rfl
  mul_smul g h p := by
    apply Subtype.ext
    funext i
    show p.1 ((g * h)⁻¹ i) = p.1 (h⁻¹ (g⁻¹ i))
    rw [mul_inv_rev]
    rfl

variable {n : ℕ}

lemma smul_val (g : Equiv.Perm (Fin n)) (p : OrderedConfig n) :
    (g • p).1 = p.1 ∘ ⇑g⁻¹ := rfl

instance : ContinuousConstSMul (Equiv.Perm (Fin n)) (OrderedConfig n) where
  continuous_const_smul g := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => (continuous_apply (g⁻¹ i)).comp continuous_subtype_val

lemma proj_eq_iff (p q : OrderedConfig n) :
    configProj n p = configProj n q ↔ p ∈ MulAction.orbit (Equiv.Perm (Fin n)) q := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    refine ⟨g, ?_⟩
    apply Subtype.ext
    rw [smul_val, hg]
    funext i
    simp
  · rintro ⟨g, rfl⟩
    apply Quotient.sound
    refine ⟨g, ?_⟩
    funext i
    simp [smul_val]

/-- The action is free: a permutation fixing an injective tuple is the identity. -/
lemma smul_eq_self (p : OrderedConfig n) (g : Equiv.Perm (Fin n)) (h : g • p = p) : g = 1 := by
  have h1 : ∀ i, p.1 (g⁻¹ i) = p.1 i := fun i => congrFun (congrArg Subtype.val h) i
  have h2 : ∀ i, g⁻¹ i = i := fun i => p.2 (h1 i)
  have : g⁻¹ = 1 := Equiv.ext h2
  simpa using congrArg (·⁻¹) this

/-- Around any ordered configuration there is a neighbourhood whose translates by
nontrivial permutations miss it. -/
lemma disjoint_nbhd (e : OrderedConfig n) :
    ∃ U ∈ nhds e, ∀ g : Equiv.Perm (Fin n),
      (((g • ·) '' U) ∩ U).Nonempty → g = 1 := by
  classical
  have hsep : ∀ g : Equiv.Perm (Fin n), ∃ V W : Set (OrderedConfig n),
      IsOpen V ∧ IsOpen W ∧ e ∈ V ∧ g • e ∈ W ∧ (g ≠ 1 → Disjoint V W) := by
    intro g
    by_cases hg : g = 1
    · exact ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ, Set.mem_univ _, Set.mem_univ _,
        fun h => absurd hg h⟩
    · have hne : g • e ≠ e := fun h => hg (smul_eq_self e g h)
      obtain ⟨W', V', hW', hV', hgW', heV', hd⟩ := t2_separation hne
      exact ⟨V', W', hV', hW', heV', hgW', fun _ => hd.symm⟩
  choose V W hV hW heV hgW hdisj using hsep
  refine ⟨⋂ g : Equiv.Perm (Fin n), (V g ∩ ((g • ·) ⁻¹' (W g))), ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ ?_
    · exact isOpen_iInter_of_finite fun g =>
        (hV g).inter ((hW g).preimage (continuous_const_smul g))
    · exact Set.mem_iInter.mpr fun g => ⟨heV g, hgW g⟩
  · rintro g ⟨y, ⟨u, huU, rfl⟩, hguU⟩
    by_contra hne
    have h1 := Set.mem_iInter.mp huU g
    have h2 := Set.mem_iInter.mp hguU g
    exact Set.disjoint_left.mp (hdisj g hne) h2.1 h1.2

theorem configProj_isQuotientCovering (n : ℕ) :
    IsQuotientCoveringMap (⇑(configProj n)) (Equiv.Perm (Fin n)) where
  toIsQuotientMap := isQuotientMap_quotient_mk'
  toContinuousConstSMul := inferInstance
  apply_eq_iff_mem_orbit := proj_eq_iff _ _
  disjoint := disjoint_nbhd

theorem configProj_isCoveringMap (n : ℕ) : IsCoveringMap (configProj n) :=
  (configProj_isQuotientCovering n).isCoveringMap

end CovSol

theorem _root_.solution (n : ℕ) :
    IsCoveringMap (configProj n) :=
  CovSol.configProj_isCoveringMap n

#print axioms solution
