-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lie_algebra_nilpotent_part_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:33.435968+00:00
-- url     : https://prove2.me/submissions/ab86bf93-c34f-4705-b67a-dc79376341b9

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : RankTwoSkewInNilradical := by
  intro V _ _ h hherm r f T hG a e v he hv
  have hlast : ∀ b : Fin (r + 1), b ≤ a.castSucc → b ≠ Fin.last r := by
    intro b hb hE
    have h1 : (b : ℕ) ≤ (a : ℕ) := hb
    have h2 : (b : ℕ) = r := by rw [hE]; rfl
    have := a.isLt; omega
  have hsub : Submodule.span ℂ (f '' {b | b < a.castSucc}) ≤ Submodule.span ℂ (f '' {b | b ≤ a.castSucc}) :=
    Submodule.span_mono (Set.image_mono fun b (hb : b < a.castSucc) => (le_of_lt hb : b ≤ a.castSucc))
  have heX : e ∈ Submodule.span ℂ (f '' {b | b ≤ a.castSucc}) := by
    have h1 : f a.castSucc ∈ Submodule.span ℂ (f '' {b | b ≤ a.castSucc}) :=
      Submodule.subset_span ⟨a.castSucc, (le_refl _ : a.castSucc ≤ a.castSucc), rfl⟩
    have := Submodule.add_mem _ (hsub he) h1
    simpa using this

  have hxe : ∀ x, (∀ b, b ≤ a.castSucc → h x (f b) = 0) → h x e = 0 := by
    intro x hx
    refine Submodule.span_induction (p := fun y _ => h x y = 0) ?_ ?_ ?_ ?_ heX
    · rintro y ⟨b, hb, rfl⟩; exact hx b hb
    · simp
    · intro y w _ _ hy hw; simp [hy, hw]
    · intro c y _ hy; simp [hy]
  have hev : h e v = 0 := by
    refine Submodule.span_induction (p := fun y _ => h y v = 0) ?_ ?_ ?_ ?_ heX
    · rintro y ⟨b, hb, rfl⟩; exact hv b hb
    · simp
    · intro y w _ _ hy hw; simp [hy, hw]
    · intro c y _ hy; simp [hy]
  have hfe : ∀ b, h (f b) e = 0 := by
    intro b; apply hxe; intro c hc
    rw [hG]; simp [hlast c hc]
  have hX : ∀ x, (∀ b : Fin r, h x (f b.castSucc) = 0) → rankTwoSkewOperator h e v x = h x v • e := by
    intro x hx
    have : h x e = 0 := by
      apply hxe; intro b hb
      have hb' : (b : ℕ) < r := lt_of_le_of_lt (show (b : ℕ) ≤ (a : ℕ) from hb) a.isLt
      have := hx ⟨b, hb'⟩
      simpa using this
    simp [rankTwoSkewOperator, this]
  have hYf : ∀ b, rankTwoSkewOperator h e v (f b) = h (f b) v • e := by
    intro b; simp [rankTwoSkewOperator, hfe b]
  refine ⟨heX, hX, hYf, fun b hb => by rw [hYf, hv b hb, zero_smul], ?_, ?_, ?_⟩
  · rw [hYf, ← smul_sub]; exact Submodule.smul_mem _ _ he
  · have hee : h e e = 0 := by
      apply hxe; intro b hb
      rw [hherm, hfe b]; simp
    simp [rankTwoSkewOperator, hev, hee]
  · have : h v e = 0 := by rw [hherm, hev]; simp
    simp [rankTwoSkewOperator, this]
end Formalism.HermitianLatticeCounting.P
