-- Prove2me | solution 1 for ClassicalComplexWPT.classicalComplexWeierstrassPreparation_noBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:07:56.601277+00:00
-- url     : https://prove2.me/submissions/565fa0c3-1ca0-4dcf-b794-84ab3f095669

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_EdgeCases
import Theorems.Thm_ClassicalComplexWPT_preparedPolynomial_zero
import Theorems.Thm_ClassicalComplexWPT_exists_lastSlice_eq_pow_mul
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero


attribute [local simp] ClassicalComplexWPT.preparedPolynomial_zero

set_option autoImplicit true
open Filter
open scoped Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution
    {d : ℕ} {f : Ambient 0 → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base 0 → ℂ) (u : Ambient 0 → ℂ),
      IsWeierstrassPreparation f d a u ∧
      ∀ (a' : Fin d → Base 0 → ℂ) (u' : Ambient 0 → ℂ),
        IsWeierstrassPreparation f d a' u' →
        (∀ i, a i =ᶠ[𝓝 0] a' i) ∧ u =ᶠ[𝓝 0] u' := by
  obtain ⟨v, hv, hv0, heq⟩ := exists_lastSlice_eq_pow_mul hf horder
  let a : Fin d → Base 0 → ℂ := fun _ _ ↦ 0
  let u : Ambient 0 → ℂ := fun x ↦ v x.2
  have hu : AnalyticAt ℂ u 0 := by
    have hcomp := hv.comp (f := fun x : Ambient 0 ↦ x.2)
      (analyticAt_snd : AnalyticAt ℂ (fun x : Ambient 0 ↦ x.2) 0)
    simpa [u, Function.comp_def] using hcomp
  have heqAmbient : f =ᶠ[𝓝 0] fun x ↦ u x * preparedPolynomial d a x := by
    have hpull := heq.comp_tendsto (continuousAt_snd :
      Tendsto (fun x : Ambient 0 ↦ x.2) (𝓝 0) (𝓝 0))
    filter_upwards [hpull] with x hx
    have hx0 : x.1 = 0 := Subsingleton.elim _ _
    have hxp : x = (0, x.2) := by ext <;> simp [hx0]
    rw [hxp]
    simpa [Function.comp_def, lastSlice, u, a, preparedPolynomial, hx0, mul_comm] using hx
  refine ⟨a, u, ⟨fun _ ↦ analyticAt_const, fun _ ↦ rfl, hu, ?_, heqAmbient⟩, ?_⟩
  · simpa [u] using hv0
  · intro a' u' h'
    have ha'0 := h'.2.1
    have hu' := h'.2.2.1
    have heq' := h'.2.2.2.2
    refine ⟨?_, ?_⟩
    · intro i
      filter_upwards [] with z
      have hz : z = 0 := Subsingleton.elim _ _
      simpa [a, hz] using (ha'0 i).symm
    · let v' : ℂ → ℂ := fun w ↦ u' (0, w)
      have hv' : AnalyticAt ℂ v' 0 := by
        simpa [v'] using hu'.curry_right
      let emb : ℂ → Ambient 0 := fun w ↦ (0, w)
      have hemb : Tendsto emb (𝓝 0) (𝓝 0) := by
        have hc : ContinuousAt emb 0 := by
          simpa [emb] using (continuousAt_const.prodMk continuousAt_id :
            ContinuousAt (fun w : ℂ ↦ ((0 : Base 0), w)) 0)
        rw [show (0 : Ambient 0) = emb 0 by
          apply Prod.ext
          · exact Subsingleton.elim _ _
          · rfl]
        exact hc
      have heq'Slice0 := heq'.comp_tendsto hemb
      have hcoeff : ∀ (i : Fin d) (z : Base 0), a' i z = 0 := by
        intro i z
        rw [Subsingleton.elim z 0]
        exact ha'0 i
      have heq'Slice : lastSlice f =ᶠ[𝓝 0] fun w ↦ v' w * w ^ d := by
        filter_upwards [heq'Slice0] with w hw
        simpa [Function.comp_def, emb, lastSlice, v', preparedPolynomial, hcoeff] using hw
      have hcancel : ∀ᶠ w in 𝓝[≠] 0, v w = v' w := by
        filter_upwards [heq.filter_mono nhdsWithin_le_nhds,
          heq'Slice.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
          with w hw hw' hw0
        have hw_ne : w ≠ 0 := by simpa using hw0
        apply mul_left_cancel₀ (pow_ne_zero d hw_ne)
        calc
          w ^ d * v w = lastSlice f w := hw.symm
          _ = v' w * w ^ d := hw'
          _ = w ^ d * v' w := mul_comm _ _
      have hvv' : v =ᶠ[𝓝 0] v' :=
        (hv.frequently_eq_iff_eventually_eq hv').1 hcancel.frequently
      have hpull := hvv'.comp_tendsto (continuousAt_snd :
        Tendsto (fun x : Ambient 0 ↦ x.2) (𝓝 0) (𝓝 0))
      filter_upwards [hpull] with x hx
      have hx0 : x.1 = 0 := Subsingleton.elim _ _
      have hxp : x = (0, x.2) := by ext <;> simp [hx0]
      rw [hxp]
      simpa [Function.comp_def, u, v', hx0] using hx
end ClassicalComplexWPT
