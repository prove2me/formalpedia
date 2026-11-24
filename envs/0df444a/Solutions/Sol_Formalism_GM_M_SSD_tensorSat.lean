-- Prove2me | solution 1 for Formalism.GM.M.SSD.tensorSat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:06.839798+00:00
-- url     : https://prove2.me/submissions/5ca785fa-a9bf-4128-bf06-c5930cb418e2

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_coeff_kap
import Theorems.Thm_Formalism_GM_M_SSD_kap_add
import Theorems.Thm_Formalism_GM_M_SSD_kap_smul
import Theorems.Thm_Formalism_GM_M_SSD_kap_zero
import Theorems.Thm_Formalism_GM_M_SSD_kap_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ τ : Type} [DecidableEq σ] (e : τ → σ)
namespace Formalism.GM.M.SSD
theorem _root_.solution (he : Function.Injective e) (Yq : Submodule ℚ_[p] (MvPolynomial τ ℚ_[p])) (YZs : Submodule ℤ_[p] (MvPolynomial τ ℚ_[p]))
    (hYZ : ∀ y ∈ YZs, y ∈ Yq) (hYZ' : ∀ y ∈ Yq, IsInt y → y ∈ YZs)
    (G : Set (MvPolynomial σ ℚ_[p])) (Mb : Finset (σ →₀ ℕ))
    (hG1 : ∀ g ∈ G, g.support ⊆ Mb) (hG2 : ∀ μ ∈ Mb, monomial μ 1 ∈ G) (hG3 : ∀ μ ∈ Mb, ∀ x, μ (e x) = 0)
    (zm : σ →₀ ℕ) (Q : MvPolynomial σ ℚ_[p])
    (hQ : Q ∈ Submodule.span ℚ_[p] {x | ∃ y ∈ YZs, ∃ g ∈ G, x = monomial zm 1 * rename e y * g})
    (hint : IsInt Q) :
    Q ∈ Submodule.span ℤ_[p] {x | ∃ y ∈ YZs, ∃ g ∈ G, x = monomial zm 1 * rename e y * g} := by
  classical
  set Bs := {x | ∃ y ∈ YZs, ∃ g ∈ G, x = monomial zm 1 * rename e y * g}
  have hGs : ∀ g ∈ G, ∀ w ∈ g.support, ∀ x, w (e x) = 0 := fun g hg w hw x => hG3 w (hG1 g hg hw) x

  have hrec : ∀ Q ∈ Submodule.span ℚ_[p] Bs,
      Q = ∑ μ ∈ Mb, monomial zm 1 * rename e (kap _ (F_inj e he zm μ) Q) * monomial μ 1 := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, g, hg, rfl⟩ := hx
      have hgs : g = ∑ μ ∈ Mb, monomial μ (coeff μ g) := by
        conv_lhs => rw [g.as_sum]
        exact Finset.sum_subset (hG1 g hg) (fun μ _ hμ => by rw [notMem_support_iff.mp hμ, monomial_zero])
      conv_lhs => rw [hgs, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun μ hμ => ?_)
      rw [kap_gen e he zm μ (hG3 μ hμ) y g (hGs g hg), map_smul, smul_eq_C_mul,
        show monomial μ (coeff μ g) = C (coeff μ g) * monomial μ 1 by rw [C_mul_monomial, mul_one]]
      ring
    | zero => simp [kap_zero]
    | add x y _ _ hx hy =>
      simp only [kap_add, map_add, mul_add, add_mul, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx =>
      simp only [kap_smul, map_smul, mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum]
      exact congrArg _ hx
  have hkY : ∀ μ ∈ Mb, ∀ Q ∈ Submodule.span ℚ_[p] Bs, kap _ (F_inj e he zm μ) Q ∈ Yq := by
    intro μ hμ' Q hQ
    have hμ := hG3 μ hμ'
    · induction hQ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, g, hg, rfl⟩ := hx
        rw [kap_gen e he zm μ hμ y g (hGs g hg)]
        exact Yq.smul_mem _ (hYZ y hy)
      | zero => rw [kap_zero]; exact Yq.zero_mem
      | add x y _ _ hx hy => rw [kap_add]; exact Yq.add_mem hx hy
      | smul c x _ hx => rw [kap_smul]; exact Yq.smul_mem c hx
  rw [hrec Q hQ]
  refine Submodule.sum_mem _ (fun μ hμ => Submodule.subset_span ⟨_, ?_, _, hG2 μ hμ, rfl⟩)
  apply hYZ' _ (hkY μ hμ Q hQ)
  intro n; rw [coeff_kap]; exact hint _
end Formalism.GM.M.SSD
