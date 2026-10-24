-- Prove2me | solution 1 for FunctionalInequalities.Analysis.legendre_eq_interior_sup_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:28:26.820977+00:00
-- url     : https://prove2.me/submissions/5a7b82b4-7b7c-4b1f-8881-3d593bca6b56

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section RadialClosure
open Filter Set
open scoped Topology
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- The actual conjugate of the radially closed extension is the supremum of
its genuine affine terms on the original open interior. Boundary terms are
obtained by the actual radial limit; terms outside the closure are bottom. -/
theorem solution
    {K : Set E} (hK : IsOpen K) (hKconv : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (ψ : E → EReal)
    (hrad : ∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x)))
    (hoff : ∀ x ∉ closure K, ψ x = ⊤) (y : E) :
    FunctionalInequalities.Analysis.legendre ψ y = ⨆ x ∈ K, (inner ℝ x y : EReal) - ψ x := by
  apply le_antisymm
  · apply iSup_le
    intro x
    by_cases hx : x ∈ closure K
    · have hinside : ∀ᶠ t : ℝ in 𝓝[<] 1, t • x ∈ K := by
        have hpos : ∀ᶠ t : ℝ in 𝓝[<] 1, 0 < t :=
          nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
        filter_upwards [hpos, self_mem_nhdsWithin] with t ht0 ht1
        have hi := hKconv.combo_interior_closure_mem_interior
          (by rwa [hK.interior_eq]) hx (sub_pos.mpr ht1) ht0.le (by ring : (1-t)+t=1)
        simpa only [smul_zero, zero_add, hK.interior_eq] using hi
      have hi : Tendsto (fun t : ℝ => (inner ℝ (t • x) y : EReal))
          (𝓝[<] 1) (𝓝 (inner ℝ x y : EReal)) := by
        have hc : Continuous (fun t : ℝ => (inner ℝ (t • x) y : EReal)) := by
          exact continuous_coe_real_ereal.comp
            ((continuous_id.smul continuous_const).inner continuous_const)
        simpa only [one_smul] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      have hn := (continuous_neg.tendsto (ψ x)).comp (hrad x)
      have ht : Tendsto (fun t : ℝ => (inner ℝ (t • x) y : EReal) - ψ (t • x))
          (𝓝[<] 1) (𝓝 ((inner ℝ x y : EReal) - ψ x)) := by
        simpa only [sub_eq_add_neg, Function.comp_def] using
          (EReal.continuousAt_add (p := ((inner ℝ x y : EReal), -ψ x))
            (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _))).tendsto.comp
              (hi.prodMk_nhds hn)
      apply le_of_tendsto ht
      filter_upwards [hinside] with t ht
      exact le_iSup_of_le (t • x) (le_iSup_of_le ht le_rfl)
    · simp only [hoff x hx, EReal.sub_top, bot_le]
  · apply iSup_le
    intro x
    apply iSup_le
    intro _
    exact le_iSup (fun z : E => (inner ℝ z y : EReal) - ψ z) x
