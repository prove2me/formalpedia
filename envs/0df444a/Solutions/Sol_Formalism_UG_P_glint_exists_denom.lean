-- Prove2me | solution 1 for Formalism.UG.P.glint_exists_denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:51:00.052835+00:00
-- url     : https://prove2.me/submissions/a0ecf810-49bc-4773-9580-31f0e230af21

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (A : ValuationSubring L) (g : GL n L) :
    ∃ c : A.toSubring, c ≠ 0 ∧
      (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) A.toSubring.subtype).range ∧
      (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈
        (RingHom.mapMatrix (m := n) A.toSubring.subtype).range := by
  classical
  let f : (n × n) ⊕ (n × n) → L := fun i => match i with
    | .inl p => (g : Matrix n n L) p.1 p.2
    | .inr p => ((g⁻¹ : GL n L) : Matrix n n L) p.1 p.2
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) f
  have hmem : ∀ i, (b : L) * f i ∈ A := by
    intro i
    obtain ⟨y, hy⟩ := hb i
    rw [Algebra.smul_def] at hy
    have : (b : L) * f i = (y : L) := hy.symm
    rw [this]; exact y.2
  refine ⟨⟨(b : A), (b : A).2⟩, ?_, ?_, ?_⟩
  · intro h0
    apply nonZeroDivisors.ne_zero b.2
    exact Subtype.ext (congrArg Subtype.val h0)
  · refine ⟨Matrix.of fun i j => ⟨(b : L) * (g : Matrix n n L) i j, hmem (.inl (i, j))⟩, ?_⟩
    ext i j
    simp
  · refine ⟨Matrix.of fun i j => ⟨(b : L) * ((g⁻¹ : GL n L) : Matrix n n L) i j,
      hmem (.inr (i, j))⟩, ?_⟩
    ext i j
    simp
end Formalism.UG.P
