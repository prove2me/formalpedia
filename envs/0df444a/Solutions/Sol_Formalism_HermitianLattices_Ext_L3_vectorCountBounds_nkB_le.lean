-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.vectorCountBounds.nkB_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:42.748639+00:00
-- url     : https://prove2.me/submissions/83c38545-4b82-48a1-8d85-5011e954b769

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_finite_vec
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_card_preimage_piQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_fm_smul
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_Qc_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_exists_liftv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_fm_star
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_mk_fm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_vecMul_adjugate
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_vecMul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_map_pow_le_span_sup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_of_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.vectorCountBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D : 𝓞 F} (hD : H.det = ι D) {d : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (n : 𝓞 F) (k : ℕ) (hdk : d + 1 ≤ k + 2) :
    ∃ n' : 𝓞 F, nkB 𝔭 (k + 2) d H n ≤ Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkM 𝔭 k H n' := by
  have hF : IsFixF K F := Fact.out
  have := h𝔭.isPrime
  obtain ⟨π0, hπ1, hπ2⟩ : ∃ π0 ∈ 𝔭, π0 ∉ 𝔭 ^ (1 + 1) := by
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (ne_bot h𝔭) 1)
    exact ⟨x, by simpa using hx, hx'⟩
  have hbad : ∀ x : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 2) // ¬ Qc 𝔭 (k + 2) d H x ∧
      fm (H.map (mkk K 𝔭 (k + 2))) x x = mkk K 𝔭 (k + 2) (ι n)},
      ∃ y : m → 𝓞 K, (fun i => mkk K 𝔭 (k + 2) (ι π0 * y i)) = x.1 := by
    intro x
    obtain ⟨x0, hx0⟩ := exists_liftv 𝔭 _ x.1
    have h1 := x.2.1
    rw [← hx0, Qc_mk hdk] at h1
    push Not at h1
    have h2 : ∀ i, x0 i ∈ extP K 𝔭 ^ 1 := by
      intro i
      have h3 := vecMul_mem h1 H.adjugate i
      rw [vecMul_adjugate, hD] at h3
      have h4 : star (x0 i) ∈ extP K 𝔭 ^ 1 := mem_of_mul_mem h𝔭 hDd h3
      have h5 := conjO_mem_pow hF 𝔭 1 _ h4
      rwa [← star_def, star_star] at h5
    have h3 : ∀ i, ∃ y, x0 i - ι π0 * y ∈ extP K 𝔭 ^ (k + 2) := by
      intro i
      obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (map_pow_le_span_sup h𝔭 hπ2 (k + 2) (h2 i))
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      refine ⟨y, ?_⟩
      have : x0 i - ι π0 * y = b := by rw [← e]; ring
      rw [this]; exact hb
    choose y hy using h3
    exact ⟨y, by rw [← hx0]; funext i; exact (Ideal.Quotient.eq.2 (hy i)).symm⟩
  choose Y hY using hbad
  have hval : ∀ y : m → 𝓞 K, ∃ a : 𝓞 F, ι a = fm H y y := fun y =>
    (conjO_eq_iff_mem_range hF _).1 (by rw [← star_def, ← fm_star hH])
  have hsol : ∀ x, ι (π0 * π0) * fm H (Y x) (Y x) - ι n ∈ extP K 𝔭 ^ (k + 2) := by
    intro x
    have h1 := x.2.2
    rw [← hY x, mk_fm, fm_smul hF] at h1
    exact Ideal.Quotient.eq.1 h1
  by_cases hne : Nonempty {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 2) // ¬ Qc 𝔭 (k + 2) d H x ∧
      fm (H.map (mkk K 𝔭 (k + 2))) x x = mkk K 𝔭 (k + 2) (ι n)}
  · obtain ⟨x₀⟩ := hne
    obtain ⟨n', hn'⟩ := hval (Y x₀)
    refine ⟨n', ?_⟩
    unfold nkM nkB
    rw [← card_preimage_piQ hK h𝔭 k (fun z => fm (H.map (mkk K 𝔭 k)) z z = mkk K 𝔭 k (ι n'))]
    have := finite_vec (K := K) (m := m) h𝔭 (k + 1)
    refine Nat.card_le_card_of_injective (fun x => ⟨fun i => mkk K 𝔭 (k + 1) (Y x i), ?_⟩) ?_
    · show fm (H.map (mkk K 𝔭 k)) (fun i => mkk K 𝔭 k (Y x i)) (fun i => mkk K 𝔭 k (Y x i)) = _
      rw [mk_fm]
      apply Ideal.Quotient.eq.2
      have hπ : π0 * π0 ∉ 𝔭 ^ (1 + 1 + 1) := mul_notMem h𝔭.isPrime (ne_bot h𝔭) hπ2 hπ2
      apply mem_of_mul_mem h𝔭 hπ
      have : ι (π0 * π0) * (fm H (Y x) (Y x) - ι n') = (ι (π0 * π0) * fm H (Y x) (Y x) - ι n) -
          (ι (π0 * π0) * fm H (Y x₀) (Y x₀) - ι n) := by rw [hn']; ring
      rw [this, show 1 + 1 + k = k + 2 by ring]
      exact sub_mem (hsol x) (hsol x₀)
    · intro x x' hxx
      apply Subtype.ext
      rw [← hY x, ← hY x']
      funext i
      apply Ideal.Quotient.eq.2
      have h1 : Y x i - Y x' i ∈ extP K 𝔭 ^ (k + 1) :=
        Ideal.Quotient.eq.1 (congrFun (congrArg Subtype.val hxx) i)
      have h2 : ι π0 ∈ extP K 𝔭 := Ideal.mem_map_of_mem _ hπ1
      rw [← mul_sub, pow_succ', ]
      exact Ideal.mul_mem_mul h2 h1
  · refine ⟨0, ?_⟩
    unfold nkB
    rw [not_nonempty_iff] at hne
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
end Formalism.HermitianLattices.Ext.L3.vectorCountBounds
