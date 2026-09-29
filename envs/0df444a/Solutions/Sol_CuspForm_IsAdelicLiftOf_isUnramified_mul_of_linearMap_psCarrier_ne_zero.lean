-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.isUnramified_mul_of_linearMap_psCarrier_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ca9d3d33-8259-59f1-a737-c9a089e3767b

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_isUnramified_mul_of_linearMap_psCarrier_ne_zero

set_option autoImplicit false
set_option Elab.async false

open NumberField IsDedekindDomain

namespace FrobLineAIILight

private theorem coe_borelElem_self_zero (q : ℕ) [Fact q.Prime] (u : ℚ_[q]ˣ) :
    (LocalNewvector.borelElem q u u 0 : Matrix (Fin 2) (Fin 2) ℚ_[q]) = Matrix.scalar (Fin 2) (u : ℚ_[q]) := by
  rw [LocalNewvector.coe_borelElem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

private theorem mul_borelElem_self_zero (q : ℕ) [Fact q.Prime] (u : ℚ_[q]ˣ) (y : GL (Fin 2) ℚ_[q]) :
    y * LocalNewvector.borelElem q u u 0 = LocalNewvector.borelElem q u u 0 * y := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_borelElem_self_zero]
  exact (Matrix.scalar_commute (u : ℚ_[q]) (fun r => Commute.all _ r) (y : Matrix (Fin 2) (Fin 2) ℚ_[q])).eq.symm

private theorem coe_borelElem_self_zero_mul_comm (q : ℕ) [Fact q.Prime] (u : ℚ_[q]ˣ) (B : Matrix (Fin 2) (Fin 2) ℚ_[q]) :
    (LocalNewvector.borelElem q u u 0 : Matrix (Fin 2) (Fin 2) ℚ_[q]) * B
      = B * (LocalNewvector.borelElem q u u 0 : Matrix (Fin 2) (Fin 2) ℚ_[q]) := by
  rw [coe_borelElem_self_zero]
  exact (Matrix.scalar_commute (u : ℚ_[q]) (fun r => Commute.all _ r) B).eq

private theorem mapMatrix_mul_comm_of_forall_mul_comm {α β : Type*} [Semiring α] [Semiring β] (e : α ≃+* β)
    (A : Matrix (Fin 2) (Fin 2) α) (hA : ∀ B : Matrix (Fin 2) (Fin 2) α, A * B = B * A)
    (X : Matrix (Fin 2) (Fin 2) β) :
    (e : α →+* β).mapMatrix A * X = X * (e : α →+* β).mapMatrix A := by
  obtain ⟨Y, rfl⟩ : ∃ Y : Matrix (Fin 2) (Fin 2) α, (e : α →+* β).mapMatrix Y = X :=
    ⟨(e.symm : β →+* α).mapMatrix X, by
      ext i j
      rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply,
        RingEquiv.coe_toRingHom, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]⟩
  rw [← map_mul, ← map_mul, hA]

private theorem coe_padicGL_eq_mapMatrix (q : ℕ) [Fact q.Prime] (z : GL (Fin 2) ℚ_[q]) :
    (AdelicDock.padicGL q z : Matrix (Fin 2) (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ))
      = (AdelicDock.padicRingEquiv q : ℚ_[q] →+* (AdelicDock.padicPlace q).adicCompletion ℚ).mapMatrix
          (z : Matrix (Fin 2) (Fin 2) ℚ_[q]) := by
  ext i j
  rw [AdelicDock.padicGL_apply, RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.coe_toRingHom]

private theorem localMat_padicGL_borelElem_self_zero_comm (q : ℕ) [Fact q.Prime] (u : ℚ_[q]ˣ)
    (X : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    AdelicDock.localMat (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
        (AdelicDock.padicGL q (LocalNewvector.borelElem q u u 0) : Matrix _ _ _) * X
      = X * AdelicDock.localMat (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
          (AdelicDock.padicGL q (LocalNewvector.borelElem q u u 0) : Matrix _ _ _) := by
  refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w = AdelicDock.padicPlace q
  · subst hw
    rw [AdelicDock.mapMatrix_localMat_self, coe_padicGL_eq_mapMatrix]
    exact mapMatrix_mul_comm_of_forall_mul_comm (AdelicDock.padicRingEquiv q) _
      (coe_borelElem_self_zero_mul_comm q u) _
  · rw [AdelicDock.mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ _ _ hw, one_mul, mul_one]

private theorem padicToAdelic_borelElem_self_zero_comm (q : ℕ) [Fact q.Prime] (u : ℚ_[q]ˣ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicDock.padicToAdelic q (LocalNewvector.borelElem q u u 0) : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) * x
      = x * (AdelicDock.padicToAdelic q (LocalNewvector.borelElem q u u 0) : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) := by
  have hmat : (AdelicDock.padicToAdelic q (LocalNewvector.borelElem q u u 0) : Matrix _ _ _)
      = AdelicDock.finMat (𝓞 ℚ) ℚ (AdelicDock.localMat (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
          (AdelicDock.padicGL q (LocalNewvector.borelElem q u u 0) : Matrix _ _ _)) := by
    rw [AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed, AdelicDock.padicToFinAdelic_apply,
      AdelicDock.coe_localEmbed]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hmat]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, map_mul, AdelicDock.mapMatrix_arch_finMat, one_mul, mul_one]
  · rw [map_mul, map_mul, AdelicDock.mapMatrix_fin_finMat]
    exact localMat_padicGL_borelElem_self_zero_comm q u _

private theorem isLevelZeroMatrix_padicToFinAdelic_borelElem (q : ℕ) [Fact q.Prime] (N : Ideal (𝓞 ℚ))
    (a₁ a₂ : ℚ_[q]ˣ) (x : ℚ_[q]) (h₁ : ‖(a₁ : ℚ_[q])‖ ≤ 1) (h₂ : ‖(a₂ : ℚ_[q])‖ ≤ 1) (hx : ‖x‖ ≤ 1) :
    AdelicLevel.IsLevelZeroMatrix (𝓞 ℚ) ℚ N
      (AdelicDock.padicToFinAdelic q (LocalNewvector.borelElem q a₁ a₂ x) : Matrix _ _ _) := by
  rw [AdelicDock.padicToFinAdelic_apply, AdelicDock.coe_localEmbed]
  refine ⟨fun i j w => ?_, fun w => ?_⟩
  · by_cases hw : w = AdelicDock.padicPlace q
    · subst hw
      rw [AdelicDock.localMat_apply_self, AdelicDock.padicGL_apply, ← AdelicDock.norm_le_one_iff_mem,
        LocalNewvector.coe_borelElem]
      fin_cases i <;> fin_cases j <;> simp [h₁, h₂, hx]
    · rw [AdelicDock.localMat_apply_of_ne (𝓞 ℚ) ℚ _ _ i j hw, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · by_cases hw : w = AdelicDock.padicPlace q
    · subst hw
      have h10 : (!![(a₁ : ℚ_[q]), x; 0, (a₂ : ℚ_[q])] : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = 0 := by simp
      rw [AdelicDock.localMat_apply_self, AdelicDock.padicGL_apply, LocalNewvector.coe_borelElem, h10, map_zero,
        map_zero]
      exact zero_le'
    · rw [AdelicDock.localMat_apply_of_ne (𝓞 ℚ) ℚ _ _ 1 0 hw, Matrix.one_apply_ne (by decide), map_zero]
      exact zero_le'

private theorem padicToFinAdelic_borelElem_self_zero_mem (q : ℕ) [Fact q.Prime] (N : Ideal (𝓞 ℚ)) (u : ℚ_[q]ˣ)
    (hu : ‖(u : ℚ_[q])‖ = 1) :
    AdelicDock.padicToFinAdelic q (LocalNewvector.borelElem q u u 0) ∈ AdelicLevel.finiteLevelZero (𝓞 ℚ) ℚ N := by
  have hinv : ‖((u⁻¹ : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
  rw [AdelicLevel.mem_finiteLevelZero_iff, ← map_inv, LocalNewvector.borelElem_inv]
  exact ⟨isLevelZeroMatrix_padicToFinAdelic_borelElem q N u u 0 hu.le hu.le (by simp),
    isLevelZeroMatrix_padicToFinAdelic_borelElem q N u⁻¹ u⁻¹ _ hinv.le hinv.le (by simp)⟩

private theorem borelElem_self_zero_smul_adelicSpan {M : ℕ} (hM : M ≠ 0) {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hgΦ : g.IsAdelicLiftOf Φ) (q : ℕ) [Fact q.Prime]
    (u : ℚ_[q]ˣ) (hu : ‖(u : ℚ_[q])‖ = 1) (ψ : LocalNewvector.AdelicSpan Φ) :
    LocalNewvector.borelElem q u u 0 • ψ = ψ := by
  have hgen : (AdelicDock.padicToAdelic q (LocalNewvector.borelElem q u u 0) : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
        • LocalNewvector.AdelicFnCarrier.mk Φ
      = LocalNewvector.AdelicFnCarrier.mk Φ := by
    refine LocalNewvector.AdelicFnCarrier.ext fun x => ?_
    rw [LocalNewvector.AdelicFnCarrier.toFn_smul, LocalNewvector.AdelicFnCarrier.toFn_mk,
      AdelicDock.padicToAdelic_apply]
    exact CuspForm.IsAdelicLiftOf.levelZero_inv hM hgΦ _
      (padicToFinAdelic_borelElem_self_zero_mem q (AdelicDock.ratLevel M) u hu) x
  have hfix : ∀ χ ∈ LocalNewvector.AdelicSpanSubmodule Φ,
      (AdelicDock.padicToAdelic q (LocalNewvector.borelElem q u u 0) : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) • χ
        = χ := by
    intro χ hχ
    refine Submodule.span_induction
      (fun χ' hχ' => ?_)
      (by rw [smul_zero])
      (fun χ₁ χ₂ _ _ h₁ h₂ => by rw [smul_add, h₁, h₂])
      (fun c χ' _ h => by rw [smul_comm, h]) hχ
    obtain ⟨h, rfl⟩ := hχ'
    rw [smul_smul, padicToAdelic_borelElem_self_zero_comm, ← smul_smul, hgen]
  apply LocalNewvector.AdelicSpan.ext Φ
  rw [LocalNewvector.AdelicSpan.padic_smul_def q, LocalNewvector.AdelicSpan.toFn_smul]
  exact hfix _ (ψ : LocalNewvector.AdelicSpanSubmodule Φ).2

private theorem borelElem_self_zero_smul_psCarrier (q : ℕ) [Fact q.Prime] (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (u : ℚ_[q]ˣ)
    (hu : ‖(u : ℚ_[q])‖ = 1) (F : LocalNewvector.PSCarrier q μ₁ μ₂) :
    LocalNewvector.borelElem q u u 0 • F = ((μ₁ u : ℂ) * (μ₂ u : ℂ)) • F := by
  refine LocalNewvector.PSCarrier.ext q μ₁ μ₂ fun y => ?_
  rw [LocalNewvector.PSCarrier.toFn_smul, LocalNewvector.PSCarrier.toFn_csmul, mul_borelElem_self_zero,
    LocalNewvector.apply_borelElem_mul_of_mem_principalSeries q (LocalNewvector.PSCarrier.toFn_mem q μ₁ μ₂ F),
    LocalNewvector.halfModulus_eq_one_of_norm_eq_one q hu hu, mul_one]

private theorem toFn_zero_apply (q : ℕ) [Fact q.Prime] (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (y : GL (Fin 2) ℚ_[q]) :
    LocalNewvector.PSCarrier.toFn q μ₁ μ₂ (0 : LocalNewvector.PSCarrier q μ₁ μ₂) y = 0 := rfl

private theorem isUnramified_mul_of_linearMap_psCarrier_ne_zero
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hgΦ : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) (hne : f ≠ 0) :
    LocalNewvector.IsUnramified q (μ₁ * μ₂) := by
  intro u hu
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    exact hne (LinearMap.ext fun v => Classical.byContradiction fun hv => h ⟨v, hv⟩)
  obtain ⟨y, hy⟩ : ∃ y, LocalNewvector.PSCarrier.toFn q μ₁ μ₂ (f v) y ≠ 0 := by
    by_contra h
    exact hv (LocalNewvector.PSCarrier.ext q μ₁ μ₂ fun y => Classical.byContradiction fun hy => h ⟨y, hy⟩)
  have h1 : f v = ((μ₁ u : ℂ) * (μ₂ u : ℂ)) • f v := by
    calc f v = f (LocalNewvector.borelElem q u u 0 • v) := by
            rw [borelElem_self_zero_smul_adelicSpan (NeZero.ne M) hgΦ q u hu v]
      _ = LocalNewvector.borelElem q u u 0 • f v := hf _ v
      _ = ((μ₁ u : ℂ) * (μ₂ u : ℂ)) • f v := borelElem_self_zero_smul_psCarrier q μ₁ μ₂ u hu (f v)
  have h2 : ((1 : ℂ) - (μ₁ u : ℂ) * (μ₂ u : ℂ)) • f v = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  have h3 : ((1 : ℂ) - (μ₁ u : ℂ) * (μ₂ u : ℂ)) * LocalNewvector.PSCarrier.toFn q μ₁ μ₂ (f v) y = 0 := by
    rw [← LocalNewvector.PSCarrier.toFn_csmul, h2, toFn_zero_apply]
  have h4 : (1 : ℂ) - (μ₁ u : ℂ) * (μ₂ u : ℂ) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hy
  apply Units.ext
  rw [MonoidHom.mul_apply, Units.val_mul, Units.val_one]
  exact (sub_eq_zero.mp h4).symm

end FrobLineAIILight

theorem solution
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hgΦ : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) (hne : f ≠ 0) :
    LocalNewvector.IsUnramified q (μ₁ * μ₂) :=
  FrobLineAIILight.isUnramified_mul_of_linearMap_psCarrier_ne_zero g q Φ hgΦ μ₁ μ₂ f hf hne

#print axioms solution

end S_CuspForm_IsAdelicLiftOf_isUnramified_mul_of_linearMap_psCarrier_ne_zero
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_isUnramified_mul_of_linearMap_psCarrier_ne_zero (solution)
