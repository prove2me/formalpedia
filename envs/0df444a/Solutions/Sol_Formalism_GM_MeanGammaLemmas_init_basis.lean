-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.init_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:47.98662+00:00
-- url     : https://prove2.me/submissions/3deed29c-6bce-42c1-85b6-58689785f3ad

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_initL_apply
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_initPart_eq_zero_of_lt
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution {ι : Type} (f : ι → MvPolynomial σ ℚ_[p]) (ord : ι → ℕ) (v : σ)
    (Fil : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hli : LinearIndependent ℤ_[p] f) (hord : ∀ b, HasOrder v (ord b) (f b))
    (hfil : ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = Fil e)
    (hstep : ∀ e x, x ∈ Fil e → initPart v e x = 0 → x ∈ Fil (e + 1)) (e : ℕ) :
    LinearIndepOn ℤ_[p] (fun b => initPart v e (f b)) {b | ord b = e} ∧
      Submodule.span ℤ_[p] ((fun b => initPart v e (f b)) '' {b | ord b = e}) =
        Submodule.span ℤ_[p] (initPart v e '' (Fil e : Set (MvPolynomial σ ℚ_[p]))) := by
  constructor
  · rw [linearIndepOn_iff]
    intro l hl h0
    have hlsub : l ∈ Finsupp.supported ℤ_[p] ℤ_[p] {b | e ≤ ord b} :=
      Finsupp.supported_mono (fun b hb => le_of_eq (Eq.symm hb)) hl
    have hx : Finsupp.linearCombination ℤ_[p] f l ∈ Fil e := by
      rw [← hfil, Finsupp.mem_span_image_iff_linearCombination]
      exact ⟨l, hlsub, rfl⟩
    have hinit : initPart v e (Finsupp.linearCombination ℤ_[p] f l) = 0 := by
      rw [← initL_apply, Finsupp.apply_linearCombination]
      exact h0
    have hx1 := hstep e _ hx hinit
    rw [← hfil, Finsupp.mem_span_image_iff_linearCombination] at hx1
    obtain ⟨l', hl', hll'⟩ := hx1
    have heq : l' = l := by
      have := linearIndependent_iff.mp hli (l' - l) (by rw [map_sub, hll', sub_self])
      exact sub_eq_zero.mp this
    ext b
    by_cases hb : ord b = e
    · rw [← heq, Finsupp.coe_zero, Pi.zero_apply]
      exact (Finsupp.mem_supported' _ _).mp hl' b (by simp [hb])
    · rw [Finsupp.coe_zero, Pi.zero_apply]
      exact (Finsupp.mem_supported' _ _).mp hl b hb
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      apply Submodule.subset_span
      refine ⟨f b, ?_, rfl⟩
      show f b ∈ (Fil e : Set (MvPolynomial σ ℚ_[p]))
      rw [← hfil]
      exact Submodule.subset_span ⟨b, le_of_eq (Eq.symm hb), rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) := by
        rw [hfil]
        exact hx
      have hmap : initL p v e x ∈ Submodule.span ℤ_[p] (initL p v e '' (f '' {b | e ≤ ord b})) := by
        rw [Submodule.span_image]
        exact Submodule.mem_map_of_mem hx'
      rw [initL_apply] at hmap
      refine (Submodule.span_le.mpr ?_) hmap
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      by_cases hbe : ord b = e
      · exact Submodule.subset_span ⟨b, hbe, rfl⟩
      · rw [SetLike.mem_coe, initL_apply,
          initPart_eq_zero_of_lt v e (ord b) (f b) (hord b) (lt_of_le_of_ne hb (Ne.symm hbe))]
        exact Submodule.zero_mem _
end Formalism.GM.MeanGammaLemmas
