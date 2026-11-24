-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.absNorm_discrIdeal_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:11.813094+00:00
-- url     : https://prove2.me/submissions/17f4f500-6d8e-4c3d-887a-d58ab420fe21

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_step_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_step_ge
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_conjIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {B : Submodule (𝓞 K) V} (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    (b : Basis (Fin (finrank K V)) K V) :
    ∀ (n : ℕ) (A : Submodule (𝓞 K) V), A ≤ B → A.toAddSubgroup.relIndex B.toAddSubgroup = n →
      n ≠ 0 → Ideal.absNorm (discrIdeal h A) = n ^ 2 * Ideal.absNorm (discrIdeal h B) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hAB hn hn0
  by_cases hBA : B ≤ A
  · have : A = B := le_antisymm hAB hBA
    subst this
    rw [AddSubgroup.relIndex_self] at hn
    rw [← hn, one_pow, one_mul]
  obtain ⟨y₀, hy₀B, hy₀A⟩ := SetLike.not_le_iff_exists.1 hBA
  let J : Ideal (𝓞 K) := A.comap (LinearMap.toSpanSingleton (𝓞 K) V y₀)
  have hJ : ∀ c, c ∈ J ↔ c • y₀ ∈ A := fun c => Iff.rfl
  have hJtop : J ≠ ⊤ := by
    intro hJt
    have : (1 : 𝓞 K) ∈ J := hJt ▸ Submodule.mem_top
    rw [hJ, one_smul] at this
    exact hy₀A this
  have hJbot : J ≠ ⊥ := by
    intro hJb
    obtain ⟨k, hk0, -, hk⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero
      (H := A.toAddSubgroup) (K := B.toAddSubgroup) (hn ▸ hn0) (a := y₀) hy₀B
    have h1 : (k : 𝓞 K) ∈ J := by
      rw [hJ, Nat.cast_smul_eq_nsmul]
      exact hk.1
    rw [hJb, Ideal.mem_bot] at h1
    exact hk0.ne' (by exact_mod_cast h1)
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJtop
  obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.2 hJP
  have hJ'0 : J' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hJ'
    exact hJbot hJ'
  have hnle : ¬ J' ≤ J := by
    intro hle
    have h1 : P * J' = 1 * J' := by
      rw [one_mul, ← hJ']
      exact le_antisymm (hJ' ▸ Ideal.mul_le_right) hle
    exact hP.ne_top (by rw [mul_right_cancel₀ hJ'0 h1, Ideal.one_eq_top])
  obtain ⟨c, hcJ', hcJ⟩ := SetLike.not_le_iff_exists.1 hnle
  have S : IsStep P A (A ⊔ Submodule.span (𝓞 K) {c • y₀}) (c • y₀) := by
    refine ⟨le_sup_left, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), hcJ,
      fun π hπ => ?_, fun x hx => ?_⟩
    · rw [smul_smul, ← hJ, hJ']
      exact Ideal.mul_mem_mul hπ hcJ'
    · obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.1 hw
      exact ⟨e, by rwa [add_sub_cancel_right]⟩
  have hA'B : A ⊔ Submodule.span (𝓞 K) {c • y₀} ≤ B :=
    sup_le hAB ((Submodule.span_singleton_le_iff_mem _ _).2 (B.smul_mem c hy₀B))
  have hA' : Formalism.HermitianLatticesTheory.IsIntegralLat h (A ⊔ Submodule.span (𝓞 K) {c • y₀}) :=
    fun x hx w hw => hB x (hA'B hx) w (hA'B hw)
  have hmul := AddSubgroup.relIndex_mul_relIndex A.toAddSubgroup
    (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup B.toAddSubgroup S.le hA'B
  rw [S.relIndex hP, hn] at hmul
  have hq1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  have hq0 : Ideal.absNorm P ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmul; exact hn0 hmul.symm
  have hn'0 : (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hn0 hmul.symm
  have hlt : (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup.relIndex B.toAddSubgroup < n := by
    rw [← hmul]
    have h2 : 2 ≤ Ideal.absNorm P := by omega
    nlinarith [Nat.pos_of_ne_zero hn'0]
  have hI : discrIdeal h A = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P *
      discrIdeal h (A ⊔ Submodule.span (𝓞 K) {c • y₀}) :=
    le_antisymm (step_le hK hP S hA' b) (step_ge hK hP S hA' b)
  rw [hI, map_mul, map_mul, absNorm_conjIdeal hK, ih _ hlt _ hA'B rfl hn'0, ← hmul]
  ring
end Formalism.HermitianLattices.Ext.L3.BallB
