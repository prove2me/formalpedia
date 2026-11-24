-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exr_logDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:59.860961+00:00
-- url     : https://prove2.me/submissions/b001873e-359f-4317-b929-4e9ca5a6773e

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LandauLocalOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (f h : ℂ → ℂ) (Zb : Finset ℂ) (m : ℂ → ℕ) (S : Set ℂ) (hS : IsOpen S)
    (hh : DifferentiableOn ℂ h S) (hfac : ∀ z ∈ S, f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z)
    (w : ℂ) (hwS : w ∈ S) (hwZ : w ∉ Zb) (hhw : h w ≠ 0) :
    deriv f w / f w = (∑ ρ ∈ Zb, (m ρ : ℂ) / (w - ρ)) + deriv h w / h w := by
  classical
  have hPd : ∀ s : Finset ℂ, w ∉ s → HasDerivAt (fun z => ∏ ρ ∈ s, (z - ρ) ^ m ρ)
      ((∏ ρ ∈ s, (w - ρ) ^ m ρ) * ∑ ρ ∈ s, (m ρ : ℂ) / (w - ρ)) w := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hasDerivAt_const w (1 : ℂ)
    | insert a s ha ih =>
      intro hw
      have hwa : w - a ≠ 0 := sub_ne_zero.2 fun e => hw (e ▸ Finset.mem_insert_self a s)
      have ih' := ih fun e => hw (Finset.mem_insert_of_mem e)
      have hm := (((hasDerivAt_id' w).sub_const a).pow (m a)).mul ih'
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      refine hm.congr_deriv ?_
      simp only [Pi.pow_apply]
      rcases Nat.eq_zero_or_pos (m a) with h0 | hpos
      · rw [h0]; simp
      · obtain ⟨k, hk⟩ : ∃ k, m a = k + 1 := ⟨m a - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel]
        push_cast
        field_simp
        ring
  have hPne : (∏ ρ ∈ Zb, (w - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ρ hρ => pow_ne_zero _ (sub_ne_zero.2 fun e => hwZ (e ▸ hρ))
  have hhd : HasDerivAt h (deriv h w) w := (hh.differentiableAt (hS.mem_nhds hwS)).hasDerivAt
  have hprod := (hPd Zb hwZ).mul hhd
  have hev : f =ᶠ[𝓝 w] fun z => (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z :=
    Filter.eventually_of_mem (hS.mem_nhds hwS) hfac
  have hd : deriv f w = _ := hev.deriv_eq.trans hprod.deriv
  rw [hd, hfac w hwS]
  field_simp
end Formalism.HermitianLattices.Ext.PrimesInProgressions
