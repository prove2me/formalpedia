-- Prove2me | solution 1 for CuspForm.IsNewform.exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9ec1ed6e-f8f9-5d53-bc16-eaacc165d73c

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Theorems.Thm_CuspForm_IsAdelicLiftOf_isUnramified_mul_of_linearMap_psCarrier_ne_zero
import Theorems.Thm_LocalNewvector_exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule
import Theorems.Thm_CuspForm_IsNewform_hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf
import Theorems.Thm_LocalNewvector_gl2CongruenceSubgroup_le_padicK1
import Theorems.Thm_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified
import Theorems.Thm_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1
import Theorems.Thm_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_le_of_stable
import Theorems.Thm_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd
p2m_attr_erase "instance" "FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

open NumberField

namespace UnramifiedTargetDescent

private theorem exists_le_one_mem_fixedSubmodule_padicK1_of_isUnramified_of_stable (q : ℕ) [Fact q.Prime]
    {μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ} (h₁ : LocalNewvector.IsUnramified q μ₁) (h₂ : LocalNewvector.IsUnramified q μ₂)
    (V : Submodule ℂ (LocalNewvector.PSCarrier q μ₁ μ₂))
    (hV : ∀ g : GL (Fin 2) ℚ_[q], ∀ v ∈ V, g • v ∈ V) (hb : V ≠ ⊥) :
    ∃ a ≤ 1, ∃ w ∈ V, w ≠ 0 ∧
      w ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.PSCarrier q μ₁ μ₂) := by

  have hsph : ∃ w : LocalNewvector.PSCarrier q μ₁ μ₂,
      w ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q 0) (LocalNewvector.PSCarrier q μ₁ μ₂) ∧
        w ≠ 0 := by
    have hfr := LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1 q
      ((LocalNewvector.hasCharConductor_zero_iff_isUnramified q).mpr h₁)
      ((LocalNewvector.hasCharConductor_zero_iff_isUnramified q).mpr h₂) 0
    have hne : LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q 0) (LocalNewvector.PSCarrier q μ₁ μ₂)
        ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hfr
      exact absurd hfr (by norm_num)
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  by_cases hr : (μ₁ (Units.mk0 (q : ℚ_[q]) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) : ℂ) *
      ((μ₂ (Units.mk0 (q : ℚ_[q]) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) : ℂ))⁻¹ = (q : ℂ)
  ·
    obtain ⟨w, hw, hw0⟩ := hsph
    exact ⟨0, Nat.zero_le 1, w,
      LocalNewvector.PSCarrier.fixedSubmodule_padicK1_zero_le_of_stable q h₁ h₂ hr V hV hb hw, hw0, hw⟩
  by_cases hr' : (μ₁ (Units.mk0 (q : ℚ_[q]) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) : ℂ) *
      ((μ₂ (Units.mk0 (q : ℚ_[q]) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) : ℂ))⁻¹ = ((q : ℂ))⁻¹
  ·
    obtain ⟨w, ⟨hwV, hw1, -⟩, -⟩ :=
      LocalNewvector.PSCarrier.existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable q h₁ h₂ hr' V hV hb
    rw [Submodule.mem_inf] at hwV
    refine ⟨1, le_rfl, w, hwV.1, ?_, hwV.2⟩
    rintro rfl
    have h0 : LocalNewvector.PSCarrier.toFn q μ₁ μ₂ 0 1 = 0 := rfl
    rw [h0] at hw1
    exact zero_ne_one hw1
  ·
    obtain ⟨w, hw, hw0⟩ := hsph
    have htop : V = ⊤ :=
      ((LocalNewvector.PSCarrier.isIrreducibleGLRep_of_isUnramified q μ₁ μ₂ h₁ h₂ hr hr').2 V hV).resolve_left hb
    exact ⟨0, Nat.zero_le 1, w, htop ▸ Submodule.mem_top, hw0, hw⟩

section SpanLemmas

variable (q : ℕ) [Fact q.Prime]

private theorem smul_mem_span_range (x : GL (Fin 2) ℚ_[q]) {φ' : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    {w : LocalNewvector.AdelicSpan φ'}
    (hw : w ∈ Submodule.span ℂ (Set.range fun y : GL (Fin 2) ℚ_[q] => y • LocalNewvector.AdelicSpan.self φ')) :
    x • w ∈ Submodule.span ℂ (Set.range fun y : GL (Fin 2) ℚ_[q] => y • LocalNewvector.AdelicSpan.self φ') := by
  refine Submodule.span_induction (fun w' hw' => ?_)
    (by rw [smul_zero]; exact zero_mem _) (fun a c _ _ ha hc => by rw [smul_add]; exact add_mem ha hc)
    (fun c a _ ha => by rw [smul_comm]; exact Submodule.smul_mem _ c ha) hw
  obtain ⟨y, rfl⟩ := hw'
  exact Submodule.subset_span ⟨x * y, by simp only [mul_smul]⟩

private theorem eq_zero_of_forall_apply_smul_self {φ' : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {N : Type*}
    [AddCommGroup N] [Module ℂ N] (T : LocalNewvector.AdelicSpan φ' →ₗ[ℂ] N)
    (hT : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ, T (g • LocalNewvector.AdelicSpan.self φ') = 0) : T = 0 := by
  have key : ∀ χ (hχ : χ ∈ LocalNewvector.AdelicSpanSubmodule φ'),
      T (LocalNewvector.AdelicSpan.mk φ' χ hχ) = 0 := by
    intro χ hχ
    induction hχ using Submodule.span_induction with
    | mem χ' hχ' =>
      obtain ⟨g, rfl⟩ := hχ'
      exact hT g
    | zero => exact map_zero T
    | add a c ha hc iha ihc =>
      have : LocalNewvector.AdelicSpan.mk φ' (a + c) (add_mem ha hc) =
          LocalNewvector.AdelicSpan.mk φ' a ha + LocalNewvector.AdelicSpan.mk φ' c hc := rfl
      rw [this, map_add, iha, ihc, add_zero]
    | smul r a ha iha =>
      have : LocalNewvector.AdelicSpan.mk φ' (r • a) (Submodule.smul_mem _ r ha) =
          r • LocalNewvector.AdelicSpan.mk φ' a ha := rfl
      rw [this, map_smul, iha, smul_zero]
  refine LinearMap.ext fun ψ => ?_
  exact key _ (ψ : LocalNewvector.AdelicSpanSubmodule φ').2

end SpanLemmas

section Embedding

variable (q : ℕ) [Fact q.Prime]

private theorem padicToAdelic_mul_comm_of (A : GL (Fin 2) ℚ_[q]) (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (hc : (AdelicDock.padicGL q A : Matrix (Fin 2) (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) *
        (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) : Matrix _ _ _) =
      (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) : Matrix _ _ _) *
        (AdelicDock.padicGL q A : Matrix _ _ _)) :
    AdelicDock.padicToAdelic q A * h = h * AdelicDock.padicToAdelic q A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed,
    AdelicDock.padicToFinAdelic_apply, AdelicDock.coe_localEmbed]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, map_mul, AdelicDock.mapMatrix_arch_finMat, one_mul, mul_one]
  · rw [map_mul, map_mul, AdelicDock.mapMatrix_fin_finMat]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = AdelicDock.padicPlace q
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self]
      have hh : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) =
          (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) :
            Matrix _ _ _) := by
        ext i j
        rfl
      rw [hh, hc]
    · rw [AdelicDock.mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ _ _ hw, one_mul, mul_one]

private theorem exists_padicGL_eq (B : GL (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) :
    ∃ A : GL (Fin 2) ℚ_[q], AdelicDock.padicGL q A = B := by
  refine ⟨Matrix.GeneralLinearGroup.map (AdelicDock.padicRingEquiv q).symm.toRingHom B, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicDock.padicGL_apply, Matrix.GeneralLinearGroup.map_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]

private theorem exists_eq_padicToAdelic_mul_comm (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (x : GL (Fin 2) ℚ_[q]) (g' : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ),
      g = AdelicDock.padicToAdelic q x * g' ∧
        ∀ y : GL (Fin 2) ℚ_[q], AdelicDock.padicToAdelic q y * g' = g' * AdelicDock.padicToAdelic q y := by
  obtain ⟨x, hx⟩ := exists_padicGL_eq q
    (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ g))
  refine ⟨x, (AdelicDock.padicToAdelic q x)⁻¹ * g, by rw [mul_inv_cancel_left], fun y => ?_⟩
  refine padicToAdelic_mul_comm_of q y _ ?_
  have h1 : AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
      (AdelicLevel.glFin (𝓞 ℚ) ℚ ((AdelicDock.padicToAdelic q x)⁻¹ * g)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_padicToAdelic,
      AdelicDock.finComponent_padicToFinAdelic_self, hx, inv_mul_cancel]
  rw [h1, Units.val_one, mul_one, one_mul]

end Embedding

section Lift

variable {M : ℕ} [NeZero M] (q : ℕ) [Fact q.Prime]
  (Φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)

private theorem apply_mul_padicToAdelic_of_mem_padicK1 {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hΦg : g.IsAdelicLiftOf Φ) {n : ℕ} (hn : M.factorization q ≤ n) {k : GL (Fin 2) ℚ_[q]}
    (hk : k ∈ LocalNewvector.padicK1 q n) (x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (x * AdelicDock.padicToAdelic q k) = Φ x := by
  have hmem := AdelicDock.padicToAdelic_mem_levelOne q (NeZero.ne M) hn hk
  have hfin : AdelicDock.padicToFinAdelic q k ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by
    have := Subgroup.mem_comap.mp hmem
    rwa [AdelicDock.glFin_padicToAdelic] at this
  rw [AdelicDock.padicToAdelic_apply]
  exact hΦg.2.1 _ hfin x

private theorem smooth_of_mem_span {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hΦg : g.IsAdelicLiftOf Φ) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ),
      ∃ U : Subgroup (GL (Fin 2) ℚ_[q]), IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧ ∀ u ∈ U, u • w = w := by
  have hKfix : ∀ k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q (M.factorization q),
      k • LocalNewvector.AdelicSpan.self Φ = LocalNewvector.AdelicSpan.self Φ := by
    intro k hk
    apply LocalNewvector.AdelicSpan.ext
    rw [LocalNewvector.AdelicSpan.padic_smul_def q, LocalNewvector.AdelicSpan.toFn_smul,
      LocalNewvector.AdelicSpan.toFn_self]
    refine LocalNewvector.AdelicFnCarrier.ext fun x => ?_
    rw [LocalNewvector.AdelicFnCarrier.toFn_smul, LocalNewvector.AdelicFnCarrier.toFn_mk,
      apply_mul_padicToAdelic_of_mem_padicK1 q Φ hΦg le_rfl
        (LocalNewvector.gl2CongruenceSubgroup_le_padicK1 q _ hk) x]
  intro w hw
  refine Submodule.span_induction (fun w' hw' => ?_) ⟨⊤, isOpen_univ, fun u _ => smul_zero u⟩
    (fun x y _ _ hx hy => ?_) (fun c x _ hx => ?_) hw
  · obtain ⟨x, rfl⟩ := hw'
    refine ⟨(FLT.SmoothVectors.gl2CongruenceSubgroup q (M.factorization q)).comap
      (MulAut.conj x⁻¹).toMonoidHom, ?_, fun u hu => ?_⟩
    · show IsOpen ((fun u => x⁻¹ * u * x⁻¹⁻¹) ⁻¹'
        (FLT.SmoothVectors.gl2CongruenceSubgroup q (M.factorization q) : Set (GL (Fin 2) ℚ_[q])))
      exact (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup q _).preimage
        ((continuous_const.mul continuous_id).mul continuous_const)
    · have hk : x⁻¹ * u * x⁻¹⁻¹ ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q (M.factorization q) :=
        Subgroup.mem_comap.mp hu
      rw [inv_inv] at hk
      show u • x • LocalNewvector.AdelicSpan.self _ = x • LocalNewvector.AdelicSpan.self _
      have hux : u * x = x * (x⁻¹ * u * x) := by group
      rw [smul_smul, hux, ← smul_smul, hKfix _ hk]
  · obtain ⟨U₁, hU₁, h₁⟩ := hx
    obtain ⟨U₂, hU₂, h₂⟩ := hy
    exact ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun u hu => by rw [smul_add, h₁ u hu.1, h₂ u hu.2]⟩
  · obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun u hu => by rw [smul_comm, h u hu]⟩

end Lift

end UnramifiedTargetDescent

open UnramifiedTargetDescent in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime] (hqM : q ^ 2 ∣ M)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hne : f ≠ 0) :
    ∃ u ∈ LocalNewvector.higherUnits q 0, μ₁ u ≠ 1 := by
  by_contra hcon
  have hμ₁1 : ∀ u ∈ LocalNewvector.higherUnits q 0, μ₁ u = 1 := by
    intro u hu
    by_contra h
    exact hcon ⟨u, hu, h⟩
  have h₁ : LocalNewvector.IsUnramified q μ₁ := fun u hu =>
    hμ₁1 u ((LocalNewvector.mem_higherUnits_zero_iff q).mpr hu)
  have hmul : LocalNewvector.IsUnramified q (μ₁ * μ₂) :=
    CuspForm.IsAdelicLiftOf.isUnramified_mul_of_linearMap_psCarrier_ne_zero g q Φ hΦg μ₁ μ₂ f hf hne
  have h₂ : LocalNewvector.IsUnramified q μ₂ := by
    intro u hu
    have h := hmul u hu
    rwa [MonoidHom.mul_apply, h₁ u hu, one_mul] at h

  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ, f (g₀ • LocalNewvector.AdelicSpan.self Φ) ≠ 0 := by
    by_contra hnone
    apply hne
    refine eq_zero_of_forall_apply_smul_self f fun g₀ => ?_
    by_contra h
    exact hnone ⟨g₀, h⟩
  have hΦ0 : Φ ≠ 0 := by
    rintro rfl
    apply hg₀
    have hself : LocalNewvector.AdelicSpan.self (F := ℚ) (0 : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) = 0 := by
      apply LocalNewvector.AdelicSpan.ext
      rw [LocalNewvector.AdelicSpan.toFn_self]
      refine LocalNewvector.AdelicFnCarrier.ext fun x => ?_
      rw [LocalNewvector.AdelicFnCarrier.toFn_mk]
      rfl
    rw [hself, smul_zero, map_zero]

  obtain ⟨x₀, g₁, hg₀eq, hcomm⟩ := exists_eq_padicToAdelic_mul_comm q g₀
  have hg₁ : f (g₁ • LocalNewvector.AdelicSpan.self Φ) ≠ 0 := by
    intro h0
    apply hg₀
    rw [hg₀eq, mul_smul, ← LocalNewvector.AdelicSpan.padic_smul_def, hf, h0, smul_zero]

  obtain ⟨T, hT, hTself⟩ : ∃ T : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂,
      (∀ (x : GL (Fin 2) ℚ_[q]) v, T (x • v) = x • T v) ∧ T (LocalNewvector.AdelicSpan.self Φ) ≠ 0 := by
    refine ⟨f ∘ₗ DistribSMul.toLinearMap ℂ _ g₁, fun x v => ?_, hg₁⟩
    show f (g₁ • (x • v)) = x • f (g₁ • v)
    rw [← hf, LocalNewvector.AdelicSpan.padic_smul_def, LocalNewvector.AdelicSpan.padic_smul_def, smul_smul,
      smul_smul, hcomm]

  set W : Submodule ℂ (LocalNewvector.AdelicSpan Φ) :=
    Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) with hWdef
  have hWstab : ∀ x : GL (Fin 2) ℚ_[q], ∀ w ∈ W, x • w ∈ W := fun x w hw => smul_mem_span_range q x hw
  have hselfW : LocalNewvector.AdelicSpan.self Φ ∈ W := Submodule.subset_span ⟨1, one_smul _ _⟩
  have hVstab : ∀ x : GL (Fin 2) ℚ_[q], ∀ z ∈ W.map T, x • z ∈ W.map T := by
    rintro x z ⟨w, hw, rfl⟩
    exact ⟨x • w, hWstab x w hw, hT x w⟩
  have hVne : W.map T ≠ ⊥ := by
    intro h
    apply hTself
    have hmem := Submodule.mem_map_of_mem (f := T) hselfW
    rw [h, Submodule.mem_bot] at hmem
    exact hmem

  obtain ⟨a, ha, w₀, hw₀V, hw₀, hw₀fix⟩ :=
    exists_le_one_mem_fixedSubmodule_padicK1_of_isUnramified_of_stable q h₁ h₂ (W.map T) hVstab hVne
  obtain ⟨v, hvW, hTv⟩ := Submodule.mem_map.mp hw₀V
  obtain ⟨y, hyW, hyfix, hTy⟩ :=
    LocalNewvector.exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule q μ₁ μ₂ T hT W hWstab
      (smooth_of_mem_span q Φ hΦg) a hvW (by rw [hTv]; exact hw₀fix)
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hw₀
    rw [← hTv, ← hTy, hy0, map_zero]

  have hcond := CuspForm.IsNewform.hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf
    hg Φ hΦ0 hΦg q
  have hqp : q.Prime := Fact.out
  have h2 : 2 ≤ M.factorization q := (hqp.pow_dvd_iff_le_factorization (NeZero.ne M)).mp hqM
  have hbot := hcond.2 a (by omega)
  apply hy0
  rw [← Submodule.mem_bot ℂ, ← hbot]
  exact hyfix

end S_CuspForm_IsNewform_exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd
end P2MW
export P2MW.S_CuspForm_IsNewform_exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd (solution)
