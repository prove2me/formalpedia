-- Prove2me | solution 1 for DenardoDP.NStage.sup_modulus_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:08:23.056244+00:00
-- url     : https://prove2.me/submissions/ae428125-3ca9-41c9-8004-6e55c70d2176

import Mathlib
import Definitions.Def_DenardoDP_NStage_Model

set_option autoImplicit false

open DenardoDP.Contraction in
theorem DenardoDP_sup_modulus_le_aux {Ω : Type*} {I : Type*}
    (B : I → BFun Ω → BFun Ω) (E : BFun Ω → BFun Ω) (c : ℝ)
    (hB : ∀ α, ModulusLE (B α) c)
    (hE : ∀ w x, IsLUB (Set.range fun α => B α w x) (E w x)) (u v : BFun Ω) (x : Ω) :
    E u x ≤ E v x + c * dist u v := by
  have key : ∀ α, B α u x ≤ E v x + c * dist u v := by
    intro α
    have h1 : |B α u x - B α v x| ≤ c * dist u v := by
      have h2 : ‖(B α u - B α v) x‖ ≤ ‖B α u - B α v‖ :=
        lp.norm_apply_le_norm ENNReal.top_ne_zero _ x
      have h3 := hB α u v
      rw [dist_eq_norm] at h3
      rw [Real.norm_eq_abs] at h2
      simp only [lp.coeFn_sub, Pi.sub_apply] at h2
      linarith
    have h4 : B α v x ≤ E v x := (hE v x).1 ⟨α, rfl⟩
    have := (abs_le.mp h1).2
    linarith
  have : E u x ≤ E v x + c * dist u v := by
    apply (hE u x).2
    rintro _ ⟨α, rfl⟩
    exact key α
  exact this

theorem solution {Ω : Type*} {I : Type*} [Nonempty I] (B : I → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (E : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) (c : ℝ) (hB : ∀ α, DenardoDP.Contraction.ModulusLE (B α) c)
    (hE : ∀ w x, IsLUB (Set.range fun α => B α w x) (E w x)) :
    DenardoDP.Contraction.ModulusLE E c := by
  intro u v
  obtain ⟨α⟩ := ‹Nonempty I›
  have hC : 0 ≤ c * dist u v := le_trans dist_nonneg (hB α u v)
  rw [dist_eq_norm]
  apply lp.norm_le_of_forall_le hC
  intro x
  have h1 := DenardoDP_sup_modulus_le_aux B E c hB hE u v x
  have h2 := DenardoDP_sup_modulus_le_aux B E c hB hE v u x
  rw [dist_comm v u] at h2
  simp only [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith
