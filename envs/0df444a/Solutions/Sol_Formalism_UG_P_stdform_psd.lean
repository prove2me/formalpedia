-- Prove2me | solution 1 for Formalism.UG.P.stdform_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:10.898946+00:00
-- url     : https://prove2.me/submissions/86810e4c-ad99-413f-9441-4aa8e951e40f

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Theorems.Thm_Formalism_UG_P_stdform_continuous_Q
import Theorems.Thm_Formalism_UG_P_stdform_Q_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]
variable {E : Type} [Field E]
namespace Formalism.UG.P
theorem _root_.solution (τ : E →+* ℂ) (M : Matrix n n ℂ) (hM : ∀ i j, ∃ e, τ e = M i j) (c : ℝ)
    (hpos : ∀ x : n → E, x ≠ 0 → 0 < c * stdformQ M (fun i => τ (x i))) :
    ∀ y, 0 ≤ c * stdformQ M y := by
  intro y
  have hcont : Continuous fun y => c * stdformQ M y := continuous_const.mul (stdform_continuous_Q M)
  have hall : ∀ x : n → E, 0 ≤ c * stdformQ M (fun i => τ (x i)) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [stdformQ]
    · exact (hpos x hx).le
  have hcl : IsClosed {y : n → ℂ | 0 ≤ c * stdformQ M y} := isClosed_le continuous_const hcont
  by_cases hre : ∃ e : E, (τ e).im ≠ 0
  · obtain ⟨e0, he0⟩ := hre
    have hsurj : Function.Surjective fun ab : ℝ × ℝ => (ab.1 : ℂ) + (ab.2 : ℂ) * τ e0 := by
      intro z
      refine ⟨(z.re - z.im / (τ e0).im * (τ e0).re, z.im / (τ e0).im), ?_⟩
      apply Complex.ext
      · simp
      · simp [he0]
    have hg : DenseRange fun ab : ℝ × ℝ => (ab.1 : ℂ) + (ab.2 : ℂ) * τ e0 := hsurj.denseRange
    have hq : DenseRange fun ab : ℚ × ℚ => ((ab.1 : ℝ), (ab.2 : ℝ)) :=
      Rat.denseRange_cast.prodMap Rat.denseRange_cast
    have h1 : DenseRange fun ab : ℚ × ℚ => τ ((ab.1 : E) + (ab.2 : E) * e0) := by
      have h0 := hg.comp hq ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
      convert h0 using 1
      funext ab
      simp [map_add, map_mul, map_ratCast]
    have h2 : DenseRange fun v : n → ℚ × ℚ => fun i => τ (((v i).1 : E) + ((v i).2 : E) * e0) :=
      DenseRange.piMap (fun _ => h1)
    have hsub : closure (Set.range fun v : n → ℚ × ℚ => fun i => τ (((v i).1 : E) + ((v i).2 : E) * e0)) ⊆
        {y : n → ℂ | 0 ≤ c * stdformQ M y} := by
      rw [hcl.closure_subset_iff]
      rintro _ ⟨v, rfl⟩
      exact hall fun i => ((v i).1 : E) + ((v i).2 : E) * e0
    exact hsub (by rw [h2.closure_range]; trivial)
  · push_neg at hre
    have hM' : ∀ i j, (M i j).im = 0 := fun i j => by
      obtain ⟨e, he⟩ := hM i j
      rw [← he]
      exact hre e
    have hR : ∀ r : n → ℝ, 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ)) := by
      have hclR : IsClosed {r : n → ℝ | 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ))} :=
        isClosed_le continuous_const (continuous_const.mul ((stdform_continuous_Q M).comp
          (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))))
      have hd : DenseRange fun v : n → ℚ => fun i => ((v i : ℚ) : ℝ) :=
        DenseRange.piMap (fun _ => Rat.denseRange_cast)
      have hsub : closure (Set.range fun v : n → ℚ => fun i => ((v i : ℚ) : ℝ)) ⊆
          {r : n → ℝ | 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ))} := by
        rw [hclR.closure_subset_iff]
        rintro _ ⟨v, rfl⟩
        have h3 := hall fun i => ((v i : ℚ) : E)
        simpa [map_ratCast] using h3
      intro r
      exact hsub (by rw [hd.closure_range]; trivial)
    rw [stdform_Q_real M hM' y, mul_add]
    exact add_nonneg (hR _) (hR _)
end Formalism.UG.P
