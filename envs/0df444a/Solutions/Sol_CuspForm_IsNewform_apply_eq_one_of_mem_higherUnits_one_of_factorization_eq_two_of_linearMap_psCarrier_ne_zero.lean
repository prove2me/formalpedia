-- Prove2me | solution 1 for CuspForm.IsNewform.apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/65f5d89c-7972-588c-a8a9-d0c5377c6135

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_CuspForm_IsAdelicLiftOf_isUnramified_mul_of_linearMap_psCarrier_ne_zero
import Theorems.Thm_LocalNewvector_PSCarrier_exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero
import Theorems.Thm_LocalNewvector_PSCarrier_hasNewvectorConductor_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero
p2m_attr_erase "instance" "FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

noncomputable section

namespace TamePSAtSquare

open LocalNewvector

section Transfer

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

private abbrev GA : Type := AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ

variable {Φ : GA → ℂ}

private theorem coe_finComponent (w : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finComponent (𝓞 ℚ) ℚ w g) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
      = (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rw [finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply]

private theorem glEq_of_forall_finComponent_eq {g h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (H : ∀ w : HeightOneSpectrum (𝓞 ℚ), finComponent (𝓞 ℚ) ℚ w g = finComponent (𝓞 ℚ) ℚ w h) :
    g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun ?_ i) j
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
  rw [← coe_finComponent w g, ← coe_finComponent w h, H w]

private theorem commute_of_finComponent_eq_one (v : HeightOneSpectrum (𝓞 ℚ))
    {w x : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hw : finComponent (𝓞 ℚ) ℚ v w = 1)
    (hx : ∀ w' : HeightOneSpectrum (𝓞 ℚ), w' ≠ v → finComponent (𝓞 ℚ) ℚ w' x = 1) :
    w * x = x * w := by
  refine glEq_of_forall_finComponent_eq fun w' => ?_
  rw [map_mul, map_mul]
  rcases eq_or_ne w' v with rfl | hw'
  · rw [hw, one_mul, mul_one]
  · rw [hx w' hw', mul_one, one_mul]

private theorem gl_ext_of_arch_fin {x y : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h₂ : glFin (𝓞 ℚ) ℚ x = glFin (𝓞 ℚ) ℚ y) : x = y := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)
  · exact congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) =>
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) h₁
  · exact congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) h₂

private theorem exists_padicGL_eq (q : ℕ) [Fact q.Prime] (m : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
    ∃ k : GL (Fin 2) ℚ_[q], padicGL q k = m := by
  refine ⟨Matrix.GeneralLinearGroup.map (n := Fin 2) (padicRingEquiv q).symm.toRingHom m,
    Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  rw [padicGL_apply, Matrix.GeneralLinearGroup.map_apply]
  exact (padicRingEquiv q).apply_symm_apply _

theorem exists_eq_padicToAdelic_mul_comm (q : ℕ) [Fact q.Prime] (gA : GA) :
    ∃ (k : GL (Fin 2) ℚ_[q]) (g' : GA), gA = padicToAdelic q k * g' ∧
      ∀ k' : GL (Fin 2) ℚ_[q], padicToAdelic q k' * g' = g' * padicToAdelic q k' := by
  obtain ⟨k, hk⟩ := exists_padicGL_eq q (finComponent (𝓞 ℚ) ℚ (padicPlace q) (glFin (𝓞 ℚ) ℚ gA))
  have hq1 : finComponent (𝓞 ℚ) ℚ (padicPlace q) (glFin (𝓞 ℚ) ℚ ((padicToAdelic q k)⁻¹ * gA)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, glFin_padicToAdelic, finComponent_padicToFinAdelic_self, hk,
      inv_mul_cancel]
  refine ⟨k, (padicToAdelic q k)⁻¹ * gA, (mul_inv_cancel_left _ _).symm, fun k' => ?_⟩
  generalize (padicToAdelic q k)⁻¹ * gA = g' at hq1 ⊢
  refine gl_ext_of_arch_fin ?_ ?_
  · simp only [map_mul, glArch_padicToAdelic, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_padicToAdelic]
    exact (commute_of_finComponent_eq_one (padicPlace q) hq1
      (fun w' hw' => finComponent_padicToFinAdelic_of_ne q k' hw')).symm

theorem padicK1_smul_self_eq {M : ℕ} (hM : M ≠ 0) {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hΦg : g.IsAdelicLiftOf Φ) (q : ℕ) [Fact q.Prime] {n : ℕ} (hn : M.factorization q ≤ n)
    {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ padicK1 q n) : k • AdelicSpan.self Φ = AdelicSpan.self Φ := by
  have hu : padicToFinAdelic q k ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel M) := by
    rw [← finEmbed_mem_levelOne_iff, ← padicToAdelic_apply]
    exact padicToAdelic_mem_levelOne q hM hn hk
  apply AdelicSpan.ext
  rw [AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicSpan.toFn_self]
  apply AdelicFnCarrier.ext
  intro x
  rw [AdelicFnCarrier.toFn_smul, AdelicFnCarrier.toFn_mk, padicToAdelic_apply]
  exact hΦg.level_inv _ hu x

private theorem exists_apply_smul_self_ne_zero {N : Type} [AddCommGroup N] [Module ℂ N]
    (f : AdelicSpan Φ →ₗ[ℂ] N) (hf0 : f ≠ 0) : ∃ gA : GA, f (gA • AdelicSpan.self Φ) ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hf0
  ext v
  obtain ⟨ψ, hψ⟩ := v
  change f (AdelicSpan.mk Φ ψ hψ) = 0
  induction hψ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨gA, rfl⟩ := hx
      exact hall gA
  | zero => exact map_zero f
  | add x y hx hy ihx ihy =>
      have : AdelicSpan.mk Φ (x + y) (add_mem hx hy) = AdelicSpan.mk Φ x hx + AdelicSpan.mk Φ y hy := rfl
      rw [this, map_add, ihx, ihy, add_zero]
  | smul c x hx ih =>
      have : AdelicSpan.mk Φ (c • x) (Submodule.smul_mem _ c hx) = c • AdelicSpan.mk Φ x hx := rfl
      rw [this, map_smul, ih, smul_zero]

theorem fixedSubmodule_padicK1_factorization_ne_bot {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hΦg : g.IsAdelicLiftOf Φ) (q : ℕ) [Fact q.Prime] (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : AdelicSpan Φ →ₗ[ℂ] PSCarrier q μ₁ μ₂)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (w : AdelicSpan Φ), f (x • w) = x • f w) (hf0 : f ≠ 0) :
    fixedSubmodule (padicK1 q (M.factorization q)) (PSCarrier q μ₁ μ₂) ≠ ⊥ := by
  have hM : M ≠ 0 := NeZero.ne M
  obtain ⟨gA, hgA⟩ := exists_apply_smul_self_ne_zero f hf0
  obtain ⟨k, g', rfl, hcomm⟩ := exists_eq_padicToAdelic_mul_comm q gA
  set ψ : AdelicSpan Φ := g' • AdelicSpan.self Φ with hψ
  have hψne : f ψ ≠ 0 := by
    intro h0
    apply hgA
    rw [mul_smul, ← AdelicSpan.padic_smul_def, hf, h0, smul_zero]
  have hψfix : ∀ k' ∈ padicK1 q (M.factorization q), k' • ψ = ψ := by
    intro k' hk'
    rw [hψ, AdelicSpan.padic_smul_def, ← mul_smul, hcomm k', mul_smul, ← AdelicSpan.padic_smul_def,
      padicK1_smul_self_eq hM hΦg q le_rfl hk']
  intro hbot
  apply hψne
  have hmem : f ψ ∈ fixedSubmodule (padicK1 q (M.factorization q)) (PSCarrier q μ₁ μ₂) := by
    rw [mem_fixedSubmodule_iff]
    intro k' hk'
    rw [← hf, hψfix k' hk']
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

end Transfer

theorem exists_hasCharConductor (q : ℕ) [Fact q.Prime] (μ : ℚ_[q]ˣ →* ℂˣ)
    (h : ∃ c : ℕ, ∀ u ∈ higherUnits q c, μ u = 1) : ∃ n : ℕ, HasCharConductor q μ n := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun m hm => ?_⟩
  have := Nat.find_min h hm
  push Not at this
  exact this

theorem forall_apply_eq_one_of_isUnramified_mul (q : ℕ) [Fact q.Prime] {μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ}
    (hunr : IsUnramified q (μ₁ * μ₂)) {n : ℕ} (h₁ : ∀ u ∈ higherUnits q n, μ₁ u = 1) :
    ∀ u ∈ higherUnits q n, μ₂ u = 1 := by
  intro u hu
  have h12 : (μ₁ * μ₂) u = 1 := hunr u hu.1
  rw [MonoidHom.mul_apply, h₁ u hu, one_mul] at h12
  exact h12

end TamePSAtSquare

end

open TamePSAtSquare LocalNewvector in
set_option linter.unusedVariables false in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime] (hM2 : M.factorization q = 2)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0) :
    ∀ u ∈ LocalNewvector.higherUnits q 1, μ₁ u = 1 ∧ μ₂ u = 1 := by
  classical

  have hfix2 : fixedSubmodule (padicK1 q 2) (PSCarrier q μ₁ μ₂) ≠ ⊥ := by
    have h := fixedSubmodule_padicK1_factorization_ne_bot hΦg q μ₁ μ₂ f hfequiv hf0
    rwa [hM2] at h

  have hF : ∃ w : AdelicSpan Φ, f w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hf0 (LinearMap.ext hall)
  obtain ⟨w, hw⟩ := hF
  obtain ⟨c, hc⟩ := PSCarrier.exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero q μ₁ μ₂ (f w) hw
  obtain ⟨n₁, h₁⟩ := exists_hasCharConductor q μ₁ ⟨c, fun u hu => (hc u hu).1⟩
  obtain ⟨n₂, h₂⟩ := exists_hasCharConductor q μ₂ ⟨c, fun u hu => (hc u hu).2⟩
  have hNV := PSCarrier.hasNewvectorConductor_add q h₁ h₂
  have hle : n₁ + n₂ ≤ 2 := by
    by_contra hlt
    push Not at hlt
    exact hfix2 (hNV.2 2 hlt)

  have hunr := CuspForm.IsAdelicLiftOf.isUnramified_mul_of_linearMap_psCarrier_ne_zero g q Φ hΦg μ₁ μ₂ f
    hfequiv hf0
  have hunr' : IsUnramified q (μ₂ * μ₁) := by rwa [mul_comm μ₂ μ₁]
  have hn₂ : n₂ ≤ n₁ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu, hne⟩ := h₂.2 n₁ hlt
    exact hne (forall_apply_eq_one_of_isUnramified_mul q hunr h₁.1 u hu)
  have hn₁ : n₁ ≤ n₂ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu, hne⟩ := h₁.2 n₂ hlt
    exact hne (forall_apply_eq_one_of_isUnramified_mul q hunr' h₂.1 u hu)
  intro u hu
  exact ⟨h₁.1 u (higherUnits_antitone q (by omega) hu), h₂.1 u (higherUnits_antitone q (by omega) hu)⟩

end S_CuspForm_IsNewform_apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero
end P2MW
export P2MW.S_CuspForm_IsNewform_apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero (solution)
