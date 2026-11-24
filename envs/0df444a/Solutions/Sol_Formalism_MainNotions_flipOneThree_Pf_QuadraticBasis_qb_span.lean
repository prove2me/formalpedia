-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:48.860395+00:00
-- url     : https://prove2.me/submissions/42a0dfc9-ba25-4655-8696-fc2cc60275d1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
variable {W O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution {p n' : ℕ} (hp : p.Prime) (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W))
    (cW : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hfin : j.Finite) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (cO : Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n'))
    (hθ : ∀ a : W, ¬ w ∣ θ - j a) (x : O) :
    ∃ a b c d : W, x = j a + j b * θ + j c * w + j d * θ * w := by
  letI : Algebra W O := j.toAlgebra
  haveI : Module.Finite W O := hfin
  have hsm : ∀ (r : W) (y : O), r • y = j r * y := fun r y => Algebra.smul_def r y
  let M : Submodule W O :=
    { carrier := {y | ∃ a b c d : W, y = j a + j b * θ + j c * w + j d * θ * w}
      add_mem' := by
        rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨a', b', c', d', rfl⟩
        exact ⟨a + a', b + b', c + c', d + d', by simp only [map_add]; ring⟩
      zero_mem' := ⟨0, 0, 0, 0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨a, b, c, d, rfl⟩
        exact ⟨r * a, r * b, r * c, r * d, by rw [hsm]; simp only [map_mul]; ring⟩ }
  have hJ : Ideal.span {(p : W)} ≤ Ideal.jacobson (⊥ : Ideal W) := by
    rw [← hpW.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal_le_jacobson _
  have hle : (⊤ : Submodule W O) ≤ M ⊔ Ideal.span {(p : W)} • (⊤ : Submodule W O) := by
    intro y _
    obtain ⟨a, b, y', hy⟩ := qb_S hp j w θ hpW cW hw2 hw cO hθ y
    obtain ⟨c, d, y'', hy'⟩ := qb_S hp j w θ hpW cW hw2 hw cO hθ y'
    refine Submodule.mem_sup.2 ⟨j a + j b * θ + j c * w + j d * θ * w, ⟨a, b, c, d, rfl⟩,
      (p : W) • y'', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top, ?_⟩
    rw [hsm, map_natCast, ← hw2, hy, hy']
    ring
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ hle
  exact htop (Submodule.mem_top : x ∈ ⊤)
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
