-- Prove2me | solution 1 for Formalism.REAL.omPlus_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:33:17.134844+00:00
-- url     : https://prove2.me/submissions/3b7a9525-cc5e-442b-91a8-b4f0221c2563

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_isotypic_part_le_of_forall
import Theorems.Thm_Formalism_REAL_compact_span_le_isotypic_part
import Theorems.Thm_Formalism_REAL_root_injective_of_ne
import Theorems.Thm_Formalism_REAL_re_inner_self_eq_norm_sq
import Theorems.Thm_Formalism_REAL_omega_eigenvalue_on_span
import Theorems.Thm_Formalism_REAL_glRel_kRel
import Theorems.Thm_Formalism_REAL_omEigen
import Theorems.Thm_Formalism_REAL_uGap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (hd : KDecomp) (ho : KOrth) (hk : KCasSpan) (hca : CasArr) (ha : ArrModule) :
    OmPlus := by
  intro V _ _ n ε E lam g u hg hu hΛ hfd hgap F hF
  classical
  have hA := (ha V n ε E 1).1 hg
  have hKU := (ha V n ε E 1).2 hu
  have hKR := glRel_kRel ε _ hA.1
  let ι := {p : Fin n × Fin n // p.1 < p.2 ∧ ε p.1 ≠ ε p.2}
  let W : ι → Submodule ℂ (Arr V n 1) := fun p =>
    isoPart ε (arrE E 1) {LamOf ε lam + root p.1.1 p.1.2} (arrV0 ε E u 1)
  let c : ι → ℝ := fun p => (ckv ε (LamOf ε lam + root p.1.1 p.1.2) - n - ckv ε (LamOf ε lam)) / 2
  have hcge : ∀ p : ι, g - 2 * n ≤ c p := by
    intro p
    have h1 := omEigen n ε lam p.1.1 p.1.2 (ne_of_lt p.2.1)
    have h2 := uGap n ε lam g p.1.1 p.1.2 p.2.1 p.2.2 (hgap _ _ p.2.1 p.2.2)
    simp only [c, ckv, LamOf]
    linarith
  have hWeig : ∀ p : ι, ∀ G ∈ W p, OmS ε E (0 : Fin 1) G = (c p : ℂ) • G := by
    intro p
    have hle : W p ≤ LinearMap.ker (OmS ε E (0 : Fin 1) - (c p : ℂ) • LinearMap.id) := by
      apply isotypic_part_le_of_forall
      intro y hy μ hμ hyh G hG
      rw [Set.mem_singleton_iff] at hμ
      subst hμ
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero]
      exact omega_eigenvalue_on_span hk hca ha hg hΛ hy hyh hG
    intro G hG
    have := hle hG
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at this
  have hWorth : ∀ p q : ι, p ≠ q → ∀ G ∈ W p, ∀ H ∈ W q, ⟪G, H⟫_ℂ = 0 := by
    intro p q hpq
    have hμ : LamOf ε lam + root p.1.1 p.1.2 ≠ LamOf ε lam + root q.1.1 q.1.2 := by
      intro h
      obtain ⟨e1, e2⟩ := root_injective_of_ne (ne_of_lt p.2.1) (add_left_cancel h)
      exact hpq (Subtype.ext (Prod.ext e1 e2))
    have step : W p ≤ (W q)ᗮ := by
      apply isotypic_part_le_of_forall
      intro y hy μ hμ' hyh
      rw [Set.mem_singleton_iff] at hμ'
      subst hμ'
      have hq : W q ≤ (kSpan ε (arrE E 1) y)ᗮ := by
        apply isotypic_part_le_of_forall
        intro y' hy' μ' hμ'' hyh' H hH
        rw [Set.mem_singleton_iff] at hμ''
        subst hμ''
        rw [Submodule.mem_orthogonal]
        intro G hG
        exact ho (Arr V n 1) n ε (arrE E 1) _ _ y y' hKR hKU hyh hyh' hμ G hG H hH
      intro G hG
      rw [Submodule.mem_orthogonal]
      intro H hH
      have := hq hH
      rw [Submodule.mem_orthogonal] at this
      exact inner_eq_zero_symm.mp (this G hG)
    intro G hG H hH
    have := step hG
    rw [Submodule.mem_orthogonal] at this
    exact inner_eq_zero_symm.mp (this H hH)
  have hsup : Vplus ε E (LamOf ε lam) u ≤ ⨆ p : ι, W p := by
    apply isotypic_part_le_of_forall
    intro y hy μ hμ hyh
    obtain ⟨a, b, hab, hne, rfl⟩ := hμ
    exact le_trans (compact_span_le_isotypic_part hy (Set.mem_singleton _) hyh) (le_iSup W ⟨(a, b), hab, hne⟩)
  obtain ⟨f, hfW, hfs⟩ : ∃ f : ι → Arr V n 1, (∀ p, f p ∈ W p) ∧ F = ∑ p, f p := by
    refine Submodule.iSup_induction W (motive := fun x => ∃ f : ι → Arr V n 1,
      (∀ p, f p ∈ W p) ∧ x = ∑ p, f p) (hsup hF) ?_ ?_ ?_
    · intro p x hx
      refine ⟨Pi.single p x, fun q => ?_, by simp⟩
      by_cases h : q = p
      · subst h; simpa using hx
      · simp [h]
    · exact ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
    · rintro x y ⟨f1, h1, e1⟩ ⟨f2, h2, e2⟩
      exact ⟨f1 + f2, fun p => Submodule.add_mem _ (h1 p) (h2 p),
        by rw [e1, e2, ← Finset.sum_add_distrib]; rfl⟩
  have hort : ∀ p q : ι, p ≠ q → ⟪f p, f q⟫_ℂ = 0 := fun p q h =>
    hWorth p q h _ (hfW p) _ (hfW q)
  have hOm : OmS ε E (0 : Fin 1) F = ∑ q, (c q : ℂ) • f q := by
    rw [hfs, map_sum]
    exact Finset.sum_congr rfl fun q _ => hWeig q _ (hfW q)
  have e1 : ⟪F, OmS ε E (0 : Fin 1) F⟫_ℂ = ∑ p, (c p : ℂ) * ⟪f p, f p⟫_ℂ := by
    rw [hOm, hfs, sum_inner]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_sum]
    rw [Finset.sum_eq_single p (fun q _ hq => by rw [inner_smul_right, hort p q (Ne.symm hq),
      mul_zero]) (by simp), inner_smul_right]
  have e2 : ⟪F, F⟫_ℂ = ∑ p, ⟪f p, f p⟫_ℂ := by
    conv_lhs => rw [hfs]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_sum, Finset.sum_eq_single p (fun q _ hq => hort p q (Ne.symm hq)) (by simp)]
  have hn : ‖F‖ ^ 2 = ∑ p, ‖f p‖ ^ 2 := by
    rw [← re_inner_self_eq_norm_sq, e2, Complex.re_sum]
    exact Finset.sum_congr rfl fun p _ => re_inner_self_eq_norm_sq (f p)
  have hre : (⟪F, OmS ε E (0 : Fin 1) F⟫_ℂ).re = ∑ p, c p * ‖f p‖ ^ 2 := by
    rw [e1, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.re_ofReal_mul, re_inner_self_eq_norm_sq]
  rw [hre, hn, Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hcge p) (sq_nonneg _)
end Formalism.REAL
