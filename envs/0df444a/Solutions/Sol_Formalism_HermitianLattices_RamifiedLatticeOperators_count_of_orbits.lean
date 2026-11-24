-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.count_of_orbits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:18.466664+00:00
-- url     : https://prove2.me/submissions/f086ea3a-6fea-4ae4-93d6-a5a88c8a3f10

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_fubini_over_orbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.OneDimInversion
open Finset Formalism.LogVandermondeBounds.product_first_zeroth_parts
section T1
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {R : Type} [CommRing R]
end T1
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.LogVandermondeBounds.product_first_zeroth_parts Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.OneDimInversion
section Orb
private lemma exists_reps {Γ P Q : Type} [Group Γ] [MulAction Γ P] [MulAction Γ Q] (pr : P → Q)
    (fib : Q → Finset P) (hpr : ∀ (γ : Γ) (p : P), pr (γ • p) = γ • pr p)
    (hfib : ∀ p y, p ∈ fib y ↔ pr p = y) (RQ : Finset Q)
    (hRQ : ∀ y : Q, ∃! r, r ∈ RQ ∧ r ∈ MulAction.orbit Γ y) :
    ∃ RP : Finset P, ∀ p : P, ∃! r, r ∈ RP ∧ r ∈ MulAction.orbit Γ p := by
  classical
  let rep : P → P := fun p => (Quotient.mk (MulAction.orbitRel Γ P) p).out
  have hrep : ∀ p, rep p ∈ MulAction.orbit Γ p := fun p =>
    MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel Γ P) p)
  have hrep_eq : ∀ p p', p' ∈ MulAction.orbit Γ p → rep p' = rep p := by
    intro p p' h
    simp only [rep]
    congr 1
    exact Quotient.sound (MulAction.orbitRel_apply.2 h)
  refine ⟨(RQ.biUnion fib).image rep, fun p => ?_⟩
  obtain ⟨y, ⟨hy, g, hg⟩, -⟩ := hRQ (pr p)
  refine ⟨rep p, ⟨?_, hrep p⟩, ?_⟩
  · rw [Finset.mem_image]
    refine ⟨g • p, Finset.mem_biUnion.2 ⟨y, hy, (hfib _ _).2 (by rw [hpr]; exact hg)⟩,
      hrep_eq p _ ⟨g, rfl⟩⟩
  · rintro r ⟨hr, hro⟩
    obtain ⟨p'', -, rfl⟩ := Finset.mem_image.1 hr
    calc rep p'' = rep (rep p'') := (hrep_eq p'' _ (hrep p'')).symm
      _ = rep p := hrep_eq p _ hro
end Orb
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
theorem _root_.solution : Count_orbits := by
  intro Γ A B V _ _ _ _ _ up down G RA RB hud hup hG hfA hfB hRA hRB
  classical
  letI act : MulAction Γ {x : A × B // x.2 ∈ up x.1} :=
    { smul := fun γ x => ⟨(γ • x.1.1, γ • x.1.2), hup γ x.1.1 x.1.2 x.2⟩
      one_smul := fun x => Subtype.ext (Prod.ext (one_smul Γ x.1.1) (one_smul Γ x.1.2))
      mul_smul := fun a b x => Subtype.ext (Prod.ext (mul_smul a b x.1.1) (mul_smul a b x.1.2)) }
  let fibA : A → Finset {x : A × B // x.2 ∈ up x.1} := fun a =>
    (up a).attach.map ⟨fun b => ⟨(a, b.1), b.2⟩, fun b b' h => Subtype.ext (congrArg (fun x => x.1.2) h)⟩
  let fibB : B → Finset {x : A × B // x.2 ∈ up x.1} := fun b =>
    (down b).attach.map ⟨fun a => ⟨(a.1, b), (hud a.1 b).2 a.2⟩,
      fun a a' h => Subtype.ext (congrArg (fun x => x.1.1) h)⟩
  have hfibA : ∀ p a, p ∈ fibA a ↔ p.1.1 = a := by
    intro p a
    constructor
    · intro h
      obtain ⟨b, -, rfl⟩ := Finset.mem_map.1 h
      rfl
    · intro h
      refine Finset.mem_map.2 ⟨⟨p.1.2, h ▸ p.2⟩, Finset.mem_attach _ _, ?_⟩
      exact Subtype.ext (Prod.ext h.symm rfl)
  have hfibB : ∀ p b, p ∈ fibB b ↔ p.1.2 = b := by
    intro p b
    constructor
    · intro h
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 h
      rfl
    · intro h
      refine Finset.mem_map.2 ⟨⟨p.1.1, (hud _ _).1 (h ▸ p.2)⟩, Finset.mem_attach _ _, ?_⟩
      exact Subtype.ext (Prod.ext rfl h.symm)
  let Ψ : {x : A × B // x.2 ∈ up x.1} → V := fun x => G x.1.1 x.1.2
  have hΨ : ∀ (γ : Γ) (x : {x : A × B // x.2 ∈ up x.1}), Ψ (γ • x) = Ψ x :=
    fun γ x => hG γ x.1.1 x.1.2 x.2
  obtain ⟨RP, hRP⟩ := exists_reps (Γ := Γ) (fun x : {x : A × B // x.2 ∈ up x.1} => x.1.1) fibA
    (fun _ _ => rfl) hfibA RA hRA
  have h1 := fubini_over_orbits Γ {x : A × B // x.2 ∈ up x.1} A V (fun x => x.1.1) fibA Ψ RP RA
    (fun _ _ => rfl) hfibA hΨ hfA hRP hRA
  have h2 := fubini_over_orbits Γ {x : A × B // x.2 ∈ up x.1} B V (fun x => x.1.2) fibB Ψ RP RB
    (fun _ _ => rfl) hfibB hΨ hfB hRP hRB
  have sA : ∀ a, ∑ p ∈ fibA a, Ψ p = ∑ b ∈ up a, G a b := by
    intro a
    rw [Finset.sum_map]
    exact Finset.sum_attach (up a) (fun b => G a b)
  have sB : ∀ b, ∑ p ∈ fibB b, Ψ p = ∑ a ∈ down b, G a b := by
    intro b
    rw [Finset.sum_map]
    exact Finset.sum_attach (down b) (fun a => G a b)
  simp only [sA, sB] at h1 h2
  exact h1.symm.trans h2
end Formalism.HermitianLattices.RamifiedLatticeOperators
