-- Prove2me | solution 1 for CuspForm.IsNewform.exists_quadraticTwistToExponentOne_of_sq_dvd_of_adelicLift_principalSeries_isUnramified_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/8b4fa941-9007-59e4-84d0-2f4f208f3b32

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_isNewform_descent
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Theorems.Thm_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified
import Theorems.Thm_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1
import Theorems.Thm_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable
import Theorems.Thm_LocalNewvector_exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule
import Theorems.Thm_CuspForm_IsNewform_hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf
import Theorems.Thm_HeckeCharacter_exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_qCoeff_eq_mul_of_adelicLift_fnTwist_of_mem_span_of_fixed
import Theorems.Thm_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_le_of_stable
import Theorems.Thm_CuspForm_IsAdelicLiftOf_exists_mem_span_fnTwist_fixed_padicK1_one_of_principalSeries
import Mathlib.NumberTheory.Padics.RingHoms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_exists_quadraticTwistToExponentOne_of_sq_dvd_of_adelicLift_principalSeries_isUnramified_ratio
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "instance" "FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

noncomputable section

namespace AtkinLiTwist

private theorem centralGL_eq_borelElem (q : ℕ) [Fact q.Prime] (z : ℚ_[q]ˣ) :
    LocalNewvector.centralGL q z = LocalNewvector.borelElem q z z 0 := by
  apply Units.ext
  show (algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) (z : ℚ_[q])
      = !![(z : ℚ_[q]), 0; 0, (z : ℚ_[q])]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal]

private theorem halfModulus_self (q : ℕ) [Fact q.Prime] (z : ℚ_[q]ˣ) :
    LocalNewvector.halfModulus q z z = 1 := by
  unfold LocalNewvector.halfModulus
  rw [div_self (a := ‖(z : ℚ_[q])‖) (norm_ne_zero_iff.mpr z.ne_zero)]
  simp

private theorem PSCarrier_centralCharacter (q : ℕ) [Fact q.Prime] (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) :
    ∀ (z : ℚ_[q]ˣ) (w : LocalNewvector.PSCarrier q μ₁ μ₂),
      LocalNewvector.centralGL q z • w = ((μ₁ * μ₂) z : ℂ) • w := by
  intro z w
  apply LocalNewvector.PSCarrier.ext
  intro y
  rw [LocalNewvector.PSCarrier.toFn_smul, LocalNewvector.PSCarrier.toFn_csmul]

  have hcomm : y * LocalNewvector.centralGL q z = LocalNewvector.centralGL q z * y := by
    apply Units.ext
    have hcg : ((LocalNewvector.centralGL q z : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q])
        = (algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) (z : ℚ_[q]) := rfl
    show (y.val : Matrix (Fin 2) (Fin 2) ℚ_[q]) * _ = _ * y.val
    rw [hcg]
    exact (Algebra.commutes (z : ℚ_[q]) y.val).symm
  rw [hcomm, centralGL_eq_borelElem]
  rw [LocalNewvector.apply_borelElem_mul_of_mem_principalSeries q
    (LocalNewvector.PSCarrier.toFn_mem q μ₁ μ₂ w) z z 0 y]
  rw [halfModulus_self, mul_one, MonoidHom.mul_apply, Units.val_mul]

private theorem L2p_unitsProduct {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hcent : ∀ (u : ℤ_[q]ˣ) (v : LocalNewvector.AdelicSpan Φ),
      LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • v = v) :
    ∀ u : ℤ_[q]ˣ,
      μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) * μ₂ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) = 1 := by
  have _ := hΦg

  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hf0 (LinearMap.ext fun v => (h v).trans (LinearMap.zero_apply v).symm)

  obtain ⟨y₀, hy₀⟩ : ∃ y₀, LocalNewvector.PSCarrier.toFn q μ₁ μ₂ (f v) y₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    refine hv (LocalNewvector.PSCarrier.ext q μ₁ μ₂ fun y => ?_)
    show LocalNewvector.PSCarrier.toFn q μ₁ μ₂ (f v) y
        = LocalNewvector.PSCarrier.toFn q μ₁ μ₂ (0 : LocalNewvector.PSCarrier q μ₁ μ₂) y
    rw [h y]
    rfl
  intro u
  set zu : ℚ_[q]ˣ := Units.map PadicInt.Coe.ringHom.toMonoidHom u

  have hcalc : (f v) = ((μ₁ * μ₂) zu : ℂ) • (f v) := by
    conv_lhs => rw [← hcent u v, hfequiv, PSCarrier_centralCharacter q μ₁ μ₂ zu (f v)]

  have hcalc' : LocalNewvector.PSCarrier.toFn q μ₁ μ₂ (f v) y₀
      = ((μ₁ * μ₂) zu : ℂ) * LocalNewvector.PSCarrier.toFn q μ₁ μ₂ (f v) y₀ := by
    conv_lhs => rw [hcalc]
    exact LocalNewvector.PSCarrier.toFn_csmul q μ₁ μ₂ _ _ y₀
  have hcoe : ((μ₁ * μ₂) zu : ℂ) = 1 := by
    have := hcalc'.symm
    rwa [mul_eq_right₀ hy₀] at this
  rw [← MonoidHom.mul_apply]
  exact Units.val_eq_one.mp hcoe

open NumberField AutomorphicForm LocalNewvector in
private theorem padicToAdelic_centralGL_mem_center (q : ℕ) [Fact q.Prime] (z : ℚ_[q]ˣ)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicDock.padicToAdelic q (centralGL q z) * x = x * AdelicDock.padicToAdelic q (centralGL q z) := by

  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  ·

    rw [map_mul, map_mul]
    have hM1 : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((AdelicDock.padicToAdelic q (centralGL q z)).val) = 1 := by
      have := AdelicDock.glArch_padicToAdelic q (centralGL q z)
      calc (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (AdelicDock.padicToAdelic q (centralGL q z)).val
          = (AdelicLevel.glArch (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q (centralGL q z))).val := rfl
        _ = 1 := by rw [this, Units.val_one]
    rw [hM1, one_mul, mul_one]
  ·
    rw [map_mul, map_mul]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul]

    have hMw : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (AdelicDock.padicToAdelic q (centralGL q z)).val)
        = (AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicDock.padicToFinAdelic q (centralGL q z))).val := by
      rw [AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat,
        AdelicDock.padicToFinAdelic_apply]
      rfl
    rw [hMw]
    by_cases hw : w = AdelicDock.padicPlace q
    ·
      subst hw
      rw [AdelicDock.finComponent_padicToFinAdelic_self]

      have hsc : (AdelicDock.padicGL q (centralGL q z)).val
          = (algebraMap ((AdelicDock.padicPlace q).adicCompletion ℚ)
              (Matrix (Fin 2) (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)))
                (AdelicDock.padicRingEquiv q (z : ℚ_[q])) := by
        ext i j
        rw [AdelicDock.padicGL_apply]
        show AdelicDock.padicRingEquiv q ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q]))
            (z : ℚ_[q]) i j) = _
        rw [Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
        split_ifs
        · rfl
        · exact map_zero _
      rw [hsc]
      exact Algebra.commutes _ _
    ·
      rw [AdelicDock.finComponent_padicToFinAdelic_of_ne q (centralGL q z) hw, Units.val_one,
        one_mul, mul_one]

open NumberField AutomorphicForm LocalNewvector in
private theorem padicToFinAdelic_centralGL_mem_finiteLevelZero (q : ℕ) [Fact q.Prime]
    (M : ℕ) (u : ℤ_[q]ˣ) :
    AdelicDock.padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))
      ∈ AdelicLevel.finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by

  have hbody : ∀ u' : ℤ_[q]ˣ, AdelicLevel.IsLevelZeroMatrix (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)
      ((AdelicDock.padicToFinAdelic q
        (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u'))).val) := by
    intro u'
    refine ⟨fun i j w => ?_, ?_⟩
    ·
      rw [AdelicDock.padicToFinAdelic_apply, AdelicDock.coe_localEmbed]
      by_cases hw : w = AdelicDock.padicPlace q
      · subst hw
        rw [AdelicDock.localMat_apply_self, AdelicDock.padicGL_apply]

        show AdelicDock.padicRingEquiv q
            ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) ((u' : ℤ_[q]) : ℚ_[q]) i j)
          ∈ (AdelicDock.padicPlace q).adicCompletionIntegers ℚ
        rw [Matrix.algebraMap_matrix_apply]
        split_ifs
        ·
          exact AdelicDock.padicRingEquiv_coe_mem q (u' : ℤ_[q])
        ·
          rw [map_zero]
          exact zero_mem _
      · rw [AdelicDock.localMat_apply_of_ne (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) _ i j hw,
          Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    ·
      intro w
      rw [AdelicDock.padicToFinAdelic_apply, AdelicDock.coe_localEmbed]
      by_cases hw : w = AdelicDock.padicPlace q
      · subst hw
        rw [AdelicDock.localMat_apply_self, AdelicDock.padicGL_apply]
        show Valued.v (AdelicDock.padicRingEquiv q
            ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) ((u' : ℤ_[q]) : ℚ_[q]) 1 0)) ≤ _
        rw [Matrix.algebraMap_matrix_apply, if_neg (by decide), map_zero, map_zero]
        exact zero_le'
      · rw [AdelicDock.localMat_apply_of_ne (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) _ 1 0 hw,
          Matrix.one_apply_ne (by decide), map_zero]
        exact zero_le'
  refine AdelicLevel.mem_finiteLevelZero_iff.mpr ⟨hbody u, ?_⟩

  have hinv : (AdelicDock.padicToFinAdelic q
        (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))⁻¹
      = AdelicDock.padicToFinAdelic q
        (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u⁻¹)) := by
    rw [← map_inv, ← map_inv, ← map_inv]
  rw [hinv]
  exact hbody u⁻¹

open NumberField AutomorphicForm LocalNewvector in
private theorem L2_central {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] :
    ∀ (u : ℤ_[q]ˣ) (v : LocalNewvector.AdelicSpan Φ),
      LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • v = v := by
  intro u v

  have hFn : ∀ x, Φ (x * AdelicDock.padicToAdelic q
        (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) = Φ x := by
    intro x
    rw [AdelicDock.padicToAdelic_apply]
    exact hΦg.levelZero_inv (NeZero.ne M) _
      (padicToFinAdelic_centralGL_mem_finiteLevelZero q M u) x

  set cz : AdelicGL2 (𝓞 ℚ) ℚ := AdelicDock.padicToAdelic q
    (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)) with hcz

  rw [AdelicSpan.padic_smul_def, ← hcz]

  obtain ⟨ψ, hψ⟩ := v
  apply AdelicSpan.ext
  rw [AdelicSpan.toFn_smul]
  show cz • ψ = ψ
  refine Submodule.span_induction (p := fun ψ _ => cz • ψ = ψ)
    ?_ (smul_zero cz)
    (fun x y _ _ hx hy => ?_)
    (fun c x _ hx => ?_) hψ
  ·
    intro ψ₀ hψ₀
    obtain ⟨g₀, hg₀⟩ := hψ₀
    show cz • ψ₀ = ψ₀
    subst hg₀
    rw [← mul_smul, padicToAdelic_centralGL_mem_center q _ g₀, mul_smul]
    congr 1
    exact AdelicFnCarrier.ext fun x => hFn x
  · show cz • (x + y) = x + y
    rw [smul_add, hx, hy]
  · show cz • (c • x) = c • x
    rw [smul_comm, hx]

private theorem aux_isUnramified_of_forall_units (q : ℕ) [Fact q.Prime] (μ : ℚ_[q]ˣ →* ℂˣ)
    (h : ∀ u : ℤ_[q]ˣ, μ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) = 1) :
    LocalNewvector.IsUnramified q μ := by
  intro u hu
  set z : ℤ_[q] := ⟨(u : ℚ_[q]), le_of_eq hu⟩ with hzdef
  have hz : IsUnit z := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_def]
    exact hu
  have hu0 : Units.map PadicInt.Coe.ringHom.toMonoidHom hz.unit = u := by
    apply Units.ext
    rw [Units.coe_map, hz.unit_spec]
    rfl
  rw [← hu0]
  exact h _

private theorem isOpen_padicK1 (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsOpen ((_root_.LocalNewvector.padicK1 p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hr1 : (p : ℝ) ^ (-(n : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hp1 (by simp)
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  refine Filter.mem_of_superset
    ((FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup p n).mem_nhds
      (SetLike.mem_coe.mpr (one_mem _))) ?_
  intro g hg
  obtain ⟨hg1, hg2⟩ := (FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff p).mp (SetLike.mem_coe.mp hg)

  have hδ : ∀ i j : Fin 2, ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 := by
    intro i j
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hint : ∀ (A : Matrix (Fin 2) (Fin 2) ℚ_[p]),
      (∀ i j, ‖(A - 1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) → ∀ i j, ‖A i j‖ ≤ 1 := by
    intro A hA i j
    have h := Padic.nonarchimedean (A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)
      ((1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)
    rw [sub_add_cancel] at h
    have hA' : ‖A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
      rw [← Matrix.sub_apply]; exact hA i j
    exact h.trans (max_le (hA'.trans hr1) (hδ i j))

  let A : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j =>
    ⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j, hint _ hg1 i j⟩
  let B : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j =>
    ⟨((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j, hint _ hg2 i j⟩
  have hAmap : A.map (algebraMap ℤ_[p] ℚ_[p]) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    ext i j; rfl
  have hBmap : B.map (algebraMap ℤ_[p] ℚ_[p]) =
      ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    ext i j; rfl
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := fun a b hab => by
    exact Subtype.ext (by simpa [PadicInt.algebraMap_apply] using hab)
  have hAB : A * B = 1 := by
    apply Matrix.map_injective hinj
    change (A * B).map (algebraMap ℤ_[p] ℚ_[p]) =
      (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p])
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.mul_inv g
  have hBA : B * A = 1 := by
    apply Matrix.map_injective hinj
    change (B * A).map (algebraMap ℤ_[p] ℚ_[p]) =
      (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p])
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.inv_mul g
  let y : GL (Fin 2) ℤ_[p] := ⟨A, B, hAB, hBA⟩
  have hy : Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p]) y = g :=
    Units.ext hAmap

  have hnorm : ∀ (z : ℤ_[p]), ‖(z : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) →
      z ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) := by
    intro z hz
    exact (PadicInt.norm_le_pow_iff_mem_span_pow z n).mp (by rw [PadicInt.norm_def]; exact hz)
  refine SetLike.mem_coe.mpr (_root_.LocalNewvector.mem_congruenceK1_iff.mpr ⟨y, hy, ?_, ?_⟩)
  · apply hnorm
    have h10 := hg1 1 0
    rwa [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero] at h10
  · apply hnorm
    have h11 := hg1 1 1
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at h11
    exact h11

open NumberField AutomorphicForm

private def padicGLinv (q : ℕ) [Fact q.Prime]
    (C : GL (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) : GL (Fin 2) ℚ_[q] :=
  ⟨(C.val).map (AdelicDock.padicRingEquiv q).symm,
   (C.inv).map (AdelicDock.padicRingEquiv q).symm,
   by rw [← Matrix.map_mul, C.val_inv,
        Matrix.map_one _ (map_zero (AdelicDock.padicRingEquiv q).symm)
          (map_one (AdelicDock.padicRingEquiv q).symm)],
   by rw [← Matrix.map_mul, C.inv_val,
        Matrix.map_one _ (map_zero (AdelicDock.padicRingEquiv q).symm)
          (map_one (AdelicDock.padicRingEquiv q).symm)]⟩

private theorem padicGL_padicGLinv (q : ℕ) [Fact q.Prime]
    (y : GL (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) :
    AdelicDock.padicGL q (padicGLinv q y) = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicDock.padicGL_apply]
  show (AdelicDock.padicRingEquiv q)
      (((y.val).map (AdelicDock.padicRingEquiv q).symm) i j) = y.val i j
  rw [Matrix.map_apply]
  exact (AdelicDock.padicRingEquiv q).apply_symm_apply _

private theorem aux_conj_padicToAdelic (q : ℕ) [Fact q.Prime]
    (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    ∃ g₀ : GL (Fin 2) ℚ_[q], ∀ k,
      AdelicDock.padicToAdelic q (g₀ * k * g₀⁻¹) * x = x * AdelicDock.padicToAdelic q k := by

  refine ⟨padicGLinv q (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
    (AdelicLevel.glFin (𝓞 ℚ) ℚ x)), fun k => ?_⟩
  set xq : GL (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ) :=
    AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
      (AdelicLevel.glFin (𝓞 ℚ) ℚ x)
  set g₀ : GL (Fin 2) ℚ_[q] := padicGLinv q xq with hg₀

  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?harch ?hfin
  case harch =>

    rw [RingHom.map_mul, RingHom.map_mul]
    have hM1 : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((AdelicDock.padicToAdelic q (g₀ * k * g₀⁻¹)).val) = 1 := by
      have := AdelicDock.glArch_padicToAdelic q (g₀ * k * g₀⁻¹)
      calc (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
            (AdelicDock.padicToAdelic q (g₀ * k * g₀⁻¹)).val
          = (AdelicLevel.glArch (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q (g₀ * k * g₀⁻¹))).val := rfl
        _ = 1 := by rw [this, Units.val_one]
    have hM2 : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((AdelicDock.padicToAdelic q k).val) = 1 := by
      have := AdelicDock.glArch_padicToAdelic q k
      calc (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (AdelicDock.padicToAdelic q k).val
          = (AdelicLevel.glArch (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q k)).val := rfl
        _ = 1 := by rw [this, Units.val_one]
    rw [hM1, hM2, one_mul, mul_one]
  case hfin =>
    rw [RingHom.map_mul, RingHom.map_mul]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [RingHom.map_mul, RingHom.map_mul]

    have hL : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
            (AdelicDock.padicToAdelic q (g₀ * k * g₀⁻¹)).val)
        = (AdelicLevel.finComponent (𝓞 ℚ) ℚ w
            (AdelicDock.padicToFinAdelic q (g₀ * k * g₀⁻¹))).val := by
      rw [AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat,
        AdelicDock.padicToFinAdelic_apply]; rfl
    have hR : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (AdelicDock.padicToAdelic q k).val)
        = (AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicDock.padicToFinAdelic q k)).val := by
      rw [AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat,
        AdelicDock.padicToFinAdelic_apply]; rfl
    rw [hL, hR]
    by_cases hw : w = AdelicDock.padicPlace q
    · subst hw

      rw [AdelicDock.finComponent_padicToFinAdelic_self,
        AdelicDock.finComponent_padicToFinAdelic_self]
      have hxw : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).mapMatrix
            ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix x.val) = xq.val := rfl
      rw [hxw, ← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [map_mul, map_mul, map_inv, hg₀, padicGL_padicGLinv, inv_mul_cancel_right]
    ·
      rw [AdelicDock.finComponent_padicToFinAdelic_of_ne q _ hw,
        AdelicDock.finComponent_padicToFinAdelic_of_ne q k hw,
        Units.val_one, one_mul, mul_one]

private theorem aux_generator_smooth {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime]
    (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    ∃ U : Subgroup (GL (Fin 2) ℚ_[q]), IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧
      ∀ u ∈ U, (AdelicDock.padicToAdelic q u :
          AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) •
          (x • _root_.LocalNewvector.AdelicFnCarrier.mk Φ) =
        x • _root_.LocalNewvector.AdelicFnCarrier.mk Φ := by
  obtain ⟨g₀, hconj⟩ := aux_conj_padicToAdelic q x
  have hself : ∀ k ∈ _root_.LocalNewvector.padicK1 q (M.factorization q),
      (AdelicDock.padicToAdelic q k :
        AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) •
        _root_.LocalNewvector.AdelicFnCarrier.mk Φ = _root_.LocalNewvector.AdelicFnCarrier.mk Φ := by
    intro k hk
    have hlev := AdelicDock.padicToAdelic_mem_levelOne q (NeZero.ne M) le_rfl hk
    have hfin : AdelicDock.padicToFinAdelic q k ∈
        NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ
          (AdelicDock.ratLevel M) := by
      have h1 := NumberField.AdelicLevel.mem_levelOne_iff.mp hlev
      rwa [AdelicDock.glFin_padicToAdelic] at h1
    apply _root_.LocalNewvector.AdelicFnCarrier.ext
    intro y
    rw [_root_.LocalNewvector.AdelicFnCarrier.toFn_smul,
      _root_.LocalNewvector.AdelicFnCarrier.toFn_mk, AdelicDock.padicToAdelic_apply]
    exact hΦg.level_inv _ hfin y
  refine ⟨(_root_.LocalNewvector.padicK1 q (M.factorization q)).map
      (MulAut.conj g₀).toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    have hfun : ⇑(MulAut.conj g₀).toMonoidHom =
        ⇑((Homeomorph.mulRight g₀⁻¹).trans (Homeomorph.mulLeft g₀)) := by
      funext u
      simp [MulAut.conj_apply, mul_assoc]
    rw [hfun]
    exact ((Homeomorph.mulRight g₀⁻¹).trans (Homeomorph.mulLeft g₀)).isOpenMap _
      (isOpen_padicK1 q (M.factorization q))
  · rintro u ⟨k, hk, rfl⟩
    have hc : (MulAut.conj g₀).toMonoidHom k = g₀ * k * g₀⁻¹ := rfl
    rw [hc, smul_smul, hconj k, ← smul_smul, hself k hk]

private theorem aux_span_smooth {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] :
    ∀ w ∈ (⊤ : Submodule ℂ (_root_.LocalNewvector.AdelicSpan Φ)),
      ∃ U : Subgroup (GL (Fin 2) ℚ_[q]), IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧
        ∀ u ∈ U, u • w = w := by
  intro w _
  have key : ∀ ψ : _root_.LocalNewvector.AdelicFnCarrier ℚ,
      ψ ∈ _root_.LocalNewvector.AdelicSpanSubmodule Φ →
      ∃ U : Subgroup (GL (Fin 2) ℚ_[q]), IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧
        ∀ u ∈ U, (AdelicDock.padicToAdelic q u :
            AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) • ψ = ψ := by
    intro ψ hψ
    refine Submodule.span_induction
      (fun ψ' hmem => ?_) ?_ (fun ψ₁ ψ₂ _ _ ih₁ ih₂ => ?_) (fun c ψ' _ ih => ?_) hψ
    · obtain ⟨x, rfl⟩ := hmem
      exact aux_generator_smooth Φ hΦg q x
    · exact ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun u _ => smul_zero _⟩
    · obtain ⟨U₁, hU₁o, hU₁⟩ := ih₁
      obtain ⟨U₂, hU₂o, hU₂⟩ := ih₂
      refine ⟨U₁ ⊓ U₂, ?_, fun u hu => ?_⟩
      · rw [Subgroup.coe_inf]
        exact hU₁o.inter hU₂o
      · obtain ⟨h₁, h₂⟩ := Subgroup.mem_inf.mp hu
        rw [smul_add, hU₁ u h₁, hU₂ u h₂]
    · obtain ⟨U, hUo, hU⟩ := ih
      exact ⟨U, hUo, fun u hu => by rw [smul_comm, hU u hu]⟩
  obtain ⟨U, hUo, hU⟩ :=
    key (_root_.LocalNewvector.AdelicSpan.toFn Φ w)
      (w : _root_.LocalNewvector.AdelicSpanSubmodule Φ).2
  refine ⟨U, hUo, fun u hu => ?_⟩
  apply _root_.LocalNewvector.AdelicSpan.ext
  rw [_root_.LocalNewvector.AdelicSpan.padic_smul_def,
    _root_.LocalNewvector.AdelicSpan.toFn_smul]
  exact hU u hu

private theorem Ls2_ramified {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] (hqM : q ^ 2 ∣ M) (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hratio : LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂))
    (hcond : LocalNewvector.HasNewvectorConductor q (LocalNewvector.AdelicSpan Φ) (M.factorization q)) :
    ¬ (∀ u : ℤ_[q]ˣ, μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) = 1) := by
  intro hunr
  classical

  have h₁ : _root_.LocalNewvector.IsUnramified q μ₁ := aux_isUnramified_of_forall_units q μ₁ hunr
  have h₂ : _root_.LocalNewvector.IsUnramified q μ₂ := by
    intro u hu
    have hr := hratio u hu
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at hr
    have h1u := h₁ u hu
    rw [h1u, inv_one, one_mul] at hr
    exact hr
  have h₁c : _root_.LocalNewvector.HasCharConductor q μ₁ 0 :=
    (_root_.LocalNewvector.hasCharConductor_zero_iff_isUnramified q).mpr h₁
  have h₂c : _root_.LocalNewvector.HasCharConductor q μ₂ 0 :=
    (_root_.LocalNewvector.hasCharConductor_zero_iff_isUnramified q).mpr h₂

  set W' : Submodule ℂ (_root_.LocalNewvector.PSCarrier q μ₁ μ₂) := LinearMap.range f with hW'def
  have hW' : ∀ x : GL (Fin 2) ℚ_[q], ∀ v ∈ W', x • v ∈ W' := by
    intro x v hv
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
    exact LinearMap.mem_range.mpr ⟨x • w, hfequiv x w⟩
  have hb' : W' ≠ ⊥ := by
    rw [hW'def]
    exact fun h => hf0 (LinearMap.range_eq_bot.mp h)

  have hfix_mono : _root_.LocalNewvector.fixedSubmodule (_root_.LocalNewvector.padicK1 q 0)
      (_root_.LocalNewvector.PSCarrier q μ₁ μ₂) ≤
      _root_.LocalNewvector.fixedSubmodule (_root_.LocalNewvector.padicK1 q 1)
        (_root_.LocalNewvector.PSCarrier q μ₁ μ₂) := by
    intro v hv
    rw [_root_.LocalNewvector.mem_fixedSubmodule_iff] at hv ⊢
    exact fun k hk => hv k (_root_.LocalNewvector.congruenceK1_antitone (by omega) hk)

  obtain ⟨z, hzW, hzfix, hz0⟩ : ∃ z, z ∈ W' ∧
      z ∈ _root_.LocalNewvector.fixedSubmodule (_root_.LocalNewvector.padicK1 q 1)
        (_root_.LocalNewvector.PSCarrier q μ₁ μ₂) ∧ z ≠ 0 := by
    by_cases hq1 : (μ₁ (Units.mk0 (q : ℚ_[q]) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) : ℂ) *
      ((μ₂ (Units.mk0 (q : ℚ_[q]) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) : ℂ))⁻¹ = (q : ℂ)
    ·
      have hle := _root_.LocalNewvector.PSCarrier.fixedSubmodule_padicK1_zero_le_of_stable
        q h₁ h₂ hq1 W' hW' hb'
      have hfr := _root_.LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1 q h₁c h₂c 0
      norm_num at hfr
      have hnb : _root_.LocalNewvector.fixedSubmodule (_root_.LocalNewvector.padicK1 q 0)
          (_root_.LocalNewvector.PSCarrier q μ₁ μ₂) ≠ ⊥ := by
        intro hbot
        rw [hbot, finrank_bot] at hfr
        omega
      obtain ⟨z, hz, hz0⟩ := Submodule.ne_bot_iff _ |>.mp hnb
      exact ⟨z, hle hz, hfix_mono hz, hz0⟩
    · by_cases hq2 : (μ₁ (Units.mk0 (q : ℚ_[q]) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) : ℂ) *
      ((μ₂ (Units.mk0 (q : ℚ_[q]) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) : ℂ))⁻¹ = ((q : ℂ))⁻¹
      ·
        obtain ⟨f₀, ⟨hf₀mem, hf₀1, -⟩, -⟩ :=
          _root_.LocalNewvector.PSCarrier.existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable
            q h₁ h₂ hq2 W' hW' hb'
        obtain ⟨hzW, hzfix⟩ := Submodule.mem_inf.mp hf₀mem
        refine ⟨f₀, hzW, hzfix, fun h0 => ?_⟩
        rw [h0] at hf₀1
        have hz : _root_.LocalNewvector.PSCarrier.toFn q μ₁ μ₂ 0 1 = 0 := rfl
        rw [hz] at hf₀1
        exact zero_ne_one hf₀1
      ·
        have hirr := _root_.LocalNewvector.PSCarrier.isIrreducibleGLRep_of_isUnramified
          q μ₁ μ₂ h₁ h₂ hq1 hq2
        rcases hirr.2 W' hW' with hbotW | htopW
        · exact absurd hbotW hb'
        · have hfr := _root_.LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1 q h₁c h₂c 1
          norm_num at hfr
          have hnb : _root_.LocalNewvector.fixedSubmodule (_root_.LocalNewvector.padicK1 q 1)
              (_root_.LocalNewvector.PSCarrier q μ₁ μ₂) ≠ ⊥ := by
            intro hbot
            rw [hbot, finrank_bot] at hfr
            omega
          obtain ⟨z, hz, hz0⟩ := Submodule.ne_bot_iff _ |>.mp hnb
          exact ⟨z, htopW ▸ Submodule.mem_top, hz, hz0⟩

  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hzW
  obtain ⟨y, -, hyfix, hyTz⟩ :=
    _root_.LocalNewvector.exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule
      q μ₁ μ₂ f hfequiv ⊤ (fun x w _ => Submodule.mem_top) (aux_span_smooth Φ hΦg q) 1
      (Submodule.mem_top (x := v)) (hv.symm ▸ hzfix)

  have he2 : 2 ≤ M.factorization q :=
    (Nat.Prime.pow_dvd_iff_le_factorization Fact.out (NeZero.ne M)).mp hqM
  have hbot := hcond.2 1 (by omega)
  rw [hbot, Submodule.mem_bot] at hyfix
  have hz' : z = 0 := by
    rw [← hv, ← hyTz, hyfix, map_zero]
  exact hz0 hz'

private theorem L6_factor (q : ℕ) [Fact q.Prime] (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (hsq : ∀ u : ℤ_[q]ˣ,
      μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) * μ₂ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) = 1)
    (hratio : LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂))
    (hram : ¬ (∀ u : ℤ_[q]ˣ, μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) = 1)) :
    ∃ b : ℕ, ((Odd q ∧ b = 1) ∨ (q = 2 ∧ b = 3)) ∧
      ∃ χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ, χ₀ ≠ 1 ∧ (∀ u, χ₀ u * χ₀ u = 1) ∧
        ∀ u : ℤ_[q]ˣ,
          μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) =
            χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u) := by
  classical
  have hqp : q.Prime := Fact.out

  set ι : ℤ_[q]ˣ →* ℚ_[q]ˣ := Units.map PadicInt.Coe.ringHom.toMonoidHom with hι
  let ε : ℤ_[q]ˣ →* ℂˣ := μ₁.comp ι
  have hε : ∀ u, ε u = μ₁ (ι u) := fun u => rfl
  have hεsq : ∀ u, ε u * ε u = 1 := by
    intro u
    have hn : ‖((ι u : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by
      change ‖((u : ℤ_[q]) : ℚ_[q])‖ = 1
      rw [PadicInt.padic_norm_e_of_padicInt]
      exact PadicInt.isUnit_iff.mp u.isUnit
    have h1 := hratio (ι u) hn
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_eq_one] at h1
    have h2 := hsq u
    rw [← h1] at h2
    exact h2

  obtain ⟨b, hbdisj, hb1, hmargin⟩ : ∃ b : ℕ, ((Odd q ∧ b = 1) ∨ (q = 2 ∧ b = 3)) ∧ 1 ≤ b ∧
      (q : ℝ) ^ (-(b : ℤ)) < ‖(2 : ℤ_[q])‖ ^ 2 := by
    by_cases hq2 : q = 2
    · subst hq2
      refine ⟨3, Or.inr ⟨rfl, rfl⟩, by norm_num, ?_⟩
      have h2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by exact_mod_cast (PadicInt.norm_p (p := 2))
      rw [h2]
      norm_num
    · refine ⟨1, Or.inl ⟨hqp.odd_of_ne_two hq2, rfl⟩, le_rfl, ?_⟩
      have h2 : ‖(2 : ℤ_[q])‖ = 1 := by
        rcases (PadicInt.norm_le_one (2 : ℤ_[q])).lt_or_eq with hlt | heq
        · exfalso
          have hdvd : (q : ℤ) ∣ 2 := (PadicInt.norm_int_lt_one_iff_dvd (p := q) 2).mp (by simpa using hlt)
          have hdvd' : q ∣ 2 := by exact_mod_cast hdvd
          rcases (Nat.prime_two.eq_one_or_self_of_dvd q hdvd') with h | h
          · exact hqp.one_lt.ne' h
          · exact hq2 h
        · exact heq
      rw [h2, one_pow, Nat.cast_one, zpow_neg, zpow_one]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hqp.one_lt)
  have hb0 : b ≠ 0 := by omega

  set π : ℤ_[q]ˣ →* (ZMod (q ^ b))ˣ := Units.map (PadicInt.toZModPow b).toMonoidHom with hπ
  have hπval : ∀ u : ℤ_[q]ˣ, ((π u : (ZMod (q ^ b))ˣ) : ZMod (q ^ b)) = PadicInt.toZModPow b (u : ℤ_[q]) :=
    fun u => rfl
  have hker_sq : ∀ u : ℤ_[q]ˣ, π u = 1 → ∃ z : ℤ_[q]ˣ, u = z * z := by
    intro u hu
    have h1 : PadicInt.toZModPow b (u : ℤ_[q]) = 1 := by
      rw [← hπval u, hu, Units.val_one]
    have hmem : (u : ℤ_[q]) - 1 ∈ (Ideal.span {(q : ℤ_[q]) ^ b} : Ideal ℤ_[q]) := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, h1, sub_self]
    have hnorm1 : ‖(u : ℤ_[q]) - 1‖ ≤ (q : ℝ) ^ (-(b : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr hmem
    let F : Polynomial ℤ_[q] := Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[q])
    have hFa : ∀ z : ℤ_[q], Polynomial.aeval z F = z ^ 2 - u := by
      intro z
      simp [F]
    have hF' : Polynomial.derivative F = Polynomial.C (2 : ℤ_[q]) * Polynomial.X := by
      simp only [F, map_sub, Polynomial.derivative_X_sq, Polynomial.derivative_C, sub_zero]
    have hF'a : ∀ z : ℤ_[q], Polynomial.aeval z (Polynomial.derivative F) = 2 * z := by
      intro z
      rw [hF', map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self_apply]
    have hcond : ‖Polynomial.aeval (1 : ℤ_[q]) F‖ < ‖Polynomial.aeval (1 : ℤ_[q]) (Polynomial.derivative F)‖ ^ 2 := by
      rw [hFa, hF'a, one_pow, mul_one, norm_sub_rev]
      exact hnorm1.trans_lt hmargin
    obtain ⟨z, hz, -, -, -⟩ := hensels_lemma hcond
    rw [hFa, sub_eq_zero, sq] at hz
    have hzu : IsUnit z := by
      rw [PadicInt.isUnit_iff]
      have hu1 : ‖(u : ℤ_[q])‖ = 1 := PadicInt.isUnit_iff.mp u.isUnit
      have hzz : ‖z‖ * ‖z‖ = 1 := by rw [← norm_mul, hz, hu1]
      rcases mul_self_eq_one_iff.mp hzz with h | h
      · exact h
      · exfalso; linarith [norm_nonneg z]
    refine ⟨hzu.unit, Units.ext ?_⟩
    rw [Units.val_mul, IsUnit.unit_spec, hz]
  have hker : ∀ u : ℤ_[q]ˣ, π u = 1 → ε u = 1 := by
    intro u hu
    obtain ⟨z, rfl⟩ := hker_sq u hu
    rw [map_mul]
    exact hεsq z

  have hsurj : Function.Surjective π := by
    intro x
    obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow b) (x : ZMod (q ^ b))
    have hau : IsUnit a := by
      by_contra hna
      have hlt : ‖a‖ < 1 := PadicInt.mem_nonunits.mp (mem_nonunits_iff.mpr hna)
      obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd a).mp hlt
      have hx : (x : ZMod (q ^ b)) = (q : ZMod (q ^ b)) * PadicInt.toZModPow b c := by
        rw [← ha, hc, map_mul, map_natCast]
      have hqu : IsUnit ((q : ℕ) : ZMod (q ^ b)) := by
        refine IsUnit.of_mul_eq_one (PadicInt.toZModPow b c * ↑x⁻¹) ?_
        rw [← mul_assoc, ← hx, Units.mul_inv]
      rw [ZMod.isUnit_iff_coprime, Nat.Coprime] at hqu
      have hdvd : q ∣ Nat.gcd q (q ^ b) := Nat.dvd_gcd dvd_rfl (dvd_pow_self q hb0)
      rw [hqu, Nat.dvd_one] at hdvd
      exact hqp.one_lt.ne' hdvd
    refine ⟨hau.unit, Units.ext ?_⟩
    rw [hπval, IsUnit.unit_spec, ha]

  have hkerle : π.ker ≤ ε.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    exact hker u hu
  let χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ := π.liftOfSurjective hsurj ⟨ε, hkerle⟩
  have hχ₀ : ∀ u : ℤ_[q]ˣ, χ₀ (π u) = ε u := fun u =>
    π.liftOfRightInverse_comp_apply (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨ε, hkerle⟩ u
  refine ⟨b, hbdisj, χ₀, ?_, ?_, ?_⟩
  · intro hone
    apply hram
    intro u
    have h := hχ₀ u
    rw [hone, MonoidHom.one_apply] at h
    rw [← hε u, ← h]
  · intro x
    obtain ⟨u, rfl⟩ := hsurj x
    rw [hχ₀]
    exact hεsq u
  · intro u
    rw [hχ₀ u]
    exact (hε u).symm

private theorem L7_signChar {m : ℕ} (χ₀ : (ZMod m)ˣ →* ℂˣ) (hsq : ∀ u, χ₀ u * χ₀ u = 1) (hne : χ₀ ≠ 1) :
    ∃ χℤ : (ZMod m)ˣ →* ℤˣ, χℤ ≠ 1 ∧ ∀ u, ((χℤ u : ℤ) : ℂ) = χ₀ u := by
  have hne1 : ((-1 : ℂ)) ≠ 1 := by norm_num
  have hpm : ∀ u, (χ₀ u : ℂ) = 1 ∨ (χ₀ u : ℂ) = -1 := by
    intro u
    have h : (χ₀ u : ℂ) * (χ₀ u : ℂ) = 1 := by
      rw [← Units.val_mul, hsq u, Units.val_one]
    exact mul_self_eq_one_iff.mp h
  have hne' : ∀ {w : (ZMod m)ˣ}, (χ₀ w : ℂ) = -1 → ¬ ((χ₀ w : ℂ) = 1) :=
    fun hw hc => hne1 (hw.symm.trans hc)
  refine ⟨{ toFun := fun u => if (χ₀ u : ℂ) = 1 then 1 else -1
            map_one' := by simp
            map_mul' := fun u v => ?_ }, fun hK => hne ?_, fun u => ?_⟩
  · have huv : (χ₀ (u * v) : ℂ) = (χ₀ u : ℂ) * (χ₀ v : ℂ) := by
      rw [map_mul, Units.val_mul]
    rcases hpm u with hu | hu <;> rcases hpm v with hv | hv
    · have h3 : (χ₀ (u * v) : ℂ) = 1 := by rw [huv, hu, hv, one_mul]
      rw [if_pos h3, if_pos hu, if_pos hv, one_mul]
    · have h3 : (χ₀ (u * v) : ℂ) = -1 := by rw [huv, hu, hv, one_mul]
      rw [if_neg (hne' h3), if_pos hu, if_neg (hne' hv), one_mul]
    · have h3 : (χ₀ (u * v) : ℂ) = -1 := by rw [huv, hu, hv, mul_one]
      rw [if_neg (hne' h3), if_neg (hne' hu), if_pos hv, mul_one]
    · have h3 : (χ₀ (u * v) : ℂ) = 1 := by rw [huv, hu, hv]; norm_num
      rw [if_pos h3, if_neg (hne' hu), if_neg (hne' hv), neg_mul_neg, one_mul]
  · ext u
    simp only [MonoidHom.one_apply, Units.val_one]
    by_cases hc : (χ₀ u : ℂ) = 1
    · exact hc
    · have h1 := DFunLike.congr_fun hK u
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply] at h1
      rw [if_neg hc] at h1
      exact absurd h1 (by decide)
  · by_cases hc : (χ₀ u : ℂ) = 1
    · simp only [MonoidHom.coe_mk, OneHom.coe_mk]
      rw [if_pos hc, hc]
      simp
    · rcases hpm u with h1 | h1
      · exact absurd h1 hc
      · simp only [MonoidHom.coe_mk, OneHom.coe_mk]
        rw [if_neg hc, h1]
        simp [Units.val_neg]

private theorem R1_phiPrime
    {M M' : ℕ} [NeZero M] [NeZero M'] (hM'M : M' ∣ M)
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {h : CuspForm (CongruenceSubgroup.Gamma0 M') 2}
    (S : Finset ℕ)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (chih : CuspForm.heckeAlgebra M' 2 (↑(S ∪ M.primeFactors) : Set ℕ) →+* ℂ)
    (hchih : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ (↑(S ∪ M.primeFactors) : Set ℕ)),
      chih (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS) = ModularFormClass.qCoeff h ℓ)
    (K : Type) [Field K] [CharZero K] (φ : chig.range →+* K)
    (m : ℕ) [NeZero m] (hmM : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ M)
    (χℤ : (ZMod m)ˣ →* ℤˣ) (χK : (ZMod m)ˣ →* Kˣ)
    (hcomp : ∀ u : (ZMod m)ˣ, (χK u : K) = ((χℤ u : ℤ) : K))
    (hrel : ∀ (ℓ : ℕ) (_hℓ : ℓ.Prime) (hℓm : Nat.Coprime ℓ m), ¬ ℓ ∣ M →
      ModularFormClass.qCoeff h ℓ =
        ((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : ℂ) * ModularFormClass.qCoeff g ℓ) :
    ∃ (φ' : chih.range →+* K),
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ)))
          (hℓN' : ¬ ℓ ∣ M') (hℓS' : ℓ ∉ ((↑(S ∪ M.primeFactors) : Set ℕ))) (hℓm : Nat.Coprime ℓ m),
        φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) =
          (χK (ZMod.unitOfCoprime ℓ hℓm) : K) *
            φ' (chih.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS')) := by
  classical

  have key : ∀ t : ↥(CuspForm.heckeAlgebra M' 2 (↑(S ∪ M.primeFactors) : Set ℕ)),
      chih t ∈ chig.range := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ Algebra.adjoin ℤ
        (CuspForm.heckeGenerators M' 2 (↑(S ∪ M.primeFactors) : Set ℕ)) := hx
    induction hx' using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨ℓ, hℓ, hℓM', hℓS', rfl⟩ | ⟨q', hq'M', hq', hq'S', rfl⟩
      ·
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hℓS'
        push Not at hℓS'
        have hℓM : ¬ ℓ ∣ M := fun hd =>
          hℓS'.2 (Nat.mem_primeFactors.mpr ⟨hℓ, hd, NeZero.ne M⟩)
        have hℓSm : ℓ ∉ (↑(S ∪ M.primeFactors) : Set ℕ) := by
          simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
          push Not
          exact hℓS'
        have hchT : (⟨CuspForm.heckeTLin 2 hℓ hℓM', hx⟩ :
            ↥(CuspForm.heckeAlgebra M' 2 (↑(S ∪ M.primeFactors) : Set ℕ)))
            = CuspForm.heckeAlgebra.T hℓ hℓM' hℓSm := Subtype.ext rfl
        rw [hchT, hchih ℓ hℓ hℓM' hℓSm]
        have hℓm : Nat.Coprime ℓ m :=
          (Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun hd => hℓM (hmM ℓ hℓ hd)
        have hℓS : ℓ ∉ (↑S : Set ℕ) := fun hS => hℓS'.1 hS
        rw [hrel ℓ hℓ hℓm hℓM, ← hchig ℓ hℓ hℓM hℓS]
        exact mul_mem (intCast_mem chig.range _) (RingHom.mem_range_self chig _)
      ·
        exfalso
        apply hq'S'
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
        exact Or.inr (Nat.mem_primeFactors.mpr ⟨hq', hq'M'.trans hM'M, NeZero.ne M⟩)
    | algebraMap r =>
      have heq : (⟨algebraMap ℤ _ r, hx⟩ :
          ↥(CuspForm.heckeAlgebra M' 2 (↑(S ∪ M.primeFactors) : Set ℕ)))
          = algebraMap ℤ _ r := Subtype.ext rfl
      have h3 : chih ((algebraMap ℤ ↥(CuspForm.heckeAlgebra M' 2 (↑(S ∪ M.primeFactors) : Set ℕ))) r)
          = (r : ℂ) := eq_intCast (chih.comp (algebraMap ℤ _)) r
      rw [heq, h3]
      exact intCast_mem chig.range r
    | add z w hz hw ihz ihw =>
      have heq : (⟨z + w, hx⟩ :
          ↥(CuspForm.heckeAlgebra M' 2 (↑(S ∪ M.primeFactors) : Set ℕ)))
          = ⟨z, hz⟩ + ⟨w, hw⟩ := Subtype.ext rfl
      rw [heq, chih.map_add]
      exact add_mem (ihz hz) (ihw hw)
    | mul z w hz hw ihz ihw =>
      have heq : (⟨z * w, hx⟩ :
          ↥(CuspForm.heckeAlgebra M' 2 (↑(S ∪ M.primeFactors) : Set ℕ)))
          = ⟨z, hz⟩ * ⟨w, hw⟩ := Subtype.ext rfl
      rw [heq, chih.map_mul]
      exact mul_mem (ihz hz) (ihw hw)
  have hle : chih.range ≤ chig.range := by rintro y ⟨t, rfl⟩; exact key t
  refine ⟨φ.comp (Subring.inclusion hle), fun ℓ hℓ hℓN hℓS hℓN' hℓS' hℓm => ?_⟩
  have hval : chih (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS')
      = ((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : ℂ)
        * chig (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) := by
    rw [hchih ℓ hℓ hℓN' hℓS', hrel ℓ hℓ hℓm hℓN, hchig ℓ hℓ hℓN hℓS]
  have hphi' : (φ.comp (Subring.inclusion hle))
      (chih.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS'))
      = ((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : K)
        * φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) := by
    have harg : Subring.inclusion hle (chih.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS'))
        = ((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : ↥chig.range)
            * chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) := by
      apply Subtype.ext
      push_cast
      exact hval
    rw [RingHom.comp_apply, harg, map_mul, map_intCast]
  rw [hphi', hcomp]
  have hu2 : χℤ (ZMod.unitOfCoprime ℓ hℓm) * χℤ (ZMod.unitOfCoprime ℓ hℓm) = 1 :=
    Int.units_mul_self _
  have h2 : ((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ)
      * (χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : ℤ) = 1 := by
    rw [← Units.val_mul, hu2, Units.val_one]
  have hsqK : ((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : K)
      * ((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : K) = 1 := by
    calc ((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : K)
        * ((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : K)
        = (((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ)
            * (χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : ℤ) : K) := by push_cast; ring
      _ = 1 := by rw [h2]; exact Int.cast_one
  rw [← mul_assoc, hsqK, one_mul]

end AtkinLiTwist

open AtkinLiTwist in

theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (S : Finset ℕ)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (K : Type) [Field K] [CharZero K]
    (φ : chig.range →+* K)
    (q : ℕ) [Fact q.Prime] (hqM : q ^ 2 ∣ M)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hratio : LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂)) :
    ∃ (m : ℕ) (_ : NeZero m), ((Odd q ∧ m = q) ∨ (q = 2 ∧ m = 8)) ∧
    ∃ (χ : (ZMod m)ˣ →* Kˣ), (∀ u : (ZMod m)ˣ, χ u * χ u = 1) ∧ χ ≠ 1 ∧
    ∃ (M' : ℕ) (_ : NeZero M'),
    ∃ (h : CuspForm (CongruenceSubgroup.Gamma0 M') 2), h.IsNewform ∧ ¬ q ^ 2 ∣ M' ∧
    ∃ (S' : Finset ℕ) (chih : CuspForm.heckeAlgebra M' 2 (↑S' : Set ℕ) →+* ℂ),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M') (hℓS : ℓ ∉ (↑S' : Set ℕ)),
        chih (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff h ℓ) ∧
    ∃ (φ' : chih.range →+* K),
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ)))
          (hℓN' : ¬ ℓ ∣ M') (hℓS' : ℓ ∉ ((S' : Set ℕ))) (hℓm : Nat.Coprime ℓ m),
        φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) =
          (χ (ZMod.unitOfCoprime ℓ hℓm) : K) *
            φ' (chih.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS')) := by
  have hM0 : M ≠ 0 := NeZero.ne M
  have he2 : 2 ≤ M.factorization q := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out hM0).mp hqM

  have hcentPhi := L2_central Φ hΦg q
  have hsq := L2p_unitsProduct Φ hΦg q μ₁ μ₂ f hfequiv hf0 hcentPhi

  have hcond := CuspForm.IsNewform.hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf
    hg Φ hΦ0 hΦg q
  have hram := Ls2_ramified Φ hΦg q hqM μ₁ μ₂ f hfequiv hf0 hratio hcond

  obtain ⟨b, hbdisj, χ₀, hχ₀ne, hχ₀sq, hχ₀compat⟩ := L6_factor q μ₁ μ₂ hsq hratio hram

  obtain ⟨η, hηfin, hηmod, hηuni, hηvals, hηu, hηq⟩ :=
    HeckeCharacter.exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv
      q b χ₀

  obtain ⟨y, hy, hy₀, hfix, hcent⟩ :=
    CuspForm.IsAdelicLiftOf.exists_mem_span_fnTwist_fixed_padicK1_one_of_principalSeries
      Φ hΦg q μ₁ μ₂ f hfequiv hf0 b χ₀ hχ₀sq hχ₀compat hratio η hηu hηq

  have hae : 1 ≤ M.factorization q := le_trans one_le_two he2
  obtain ⟨h', hh'norm, hh'coeff⟩ :=
    CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_qCoeff_eq_mul_of_adelicLift_fnTwist_of_mem_span_of_fixed
      (hg.isNormalizedEigenform) q Φ hΦg η hηfin b hηmod 1 hae y hy hy₀ hfix hcent

  have hNq : q ^ (M.factorization q - 1) ∣ M :=
    (Nat.Prime.pow_dvd_iff_le_factorization Fact.out hM0).mpr (Nat.sub_le _ _)
  have hN'pos : 0 < M / q ^ (M.factorization q - 1) :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hNq) (pow_pos (Fact.out : q.Prime).pos _)
  haveI : NeZero (M / q ^ (M.factorization q - 1)) := ⟨hN'pos.ne'⟩
  obtain ⟨M', hM'div, h, hhnew, hhcoeff⟩ := CuspForm.exists_isNewform_descent h' hh'norm
  have hM'0 : M' ≠ 0 := fun e => hN'pos.ne' (Nat.eq_zero_of_zero_dvd (e ▸ hM'div))
  haveI : NeZero M' := ⟨hM'0⟩
  have hq2 : ¬ q ^ 2 ∣ M' := by
    intro hdvd
    have h1 : q ^ 2 ∣ M / q ^ (M.factorization q - 1) := hdvd.trans hM'div
    have h2 : q ^ (M.factorization q - 1) * q ^ 2 ∣ M := (Nat.dvd_div_iff_mul_dvd hNq).mp h1
    rw [← pow_add] at h2
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out hM0).mp h2
    omega
  obtain ⟨chih, _hchih_eigen, hchihT, _hchihU⟩ :=
    CuspForm.IsNormalizedEigenform.exists_ringHom_heckeAlgebra
      (hhnew.isNormalizedEigenform) (↑(S ∪ M.primeFactors) : Set ℕ)

  obtain ⟨χℤ, hχℤne, hχℤcompat⟩ := L7_signChar χ₀ hχ₀sq hχ₀ne
  have hqdvdM : q ∣ M := dvd_trans (dvd_pow_self q two_ne_zero) hqM
  have hrel : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : Nat.Coprime ℓ (q ^ b)), ¬ ℓ ∣ M →
      ModularFormClass.qCoeff h ℓ =
        ((χℤ (ZMod.unitOfCoprime ℓ hℓm) : ℤ) : ℂ) * ModularFormClass.qCoeff g ℓ := by
    intro ℓ hℓ hℓm hℓM
    have hℓq : ℓ ≠ q := fun e => hℓM (e ▸ hqdvdM)
    have hℓN' : ¬ ℓ ∣ M / q ^ (M.factorization q - 1) :=
      fun hd => hℓM (hd.trans (Nat.div_dvd_of_dvd hNq))
    rw [hhcoeff ℓ hℓ hℓN', hh'coeff ℓ hℓ hℓM hℓq, hηvals ℓ hℓ hℓq,
      ← hχℤcompat (ZMod.unitOfCoprime ℓ (Nat.Coprime.pow_right b ((Nat.coprime_primes hℓ Fact.out).mpr hℓq)))]

  haveI : NeZero (q ^ b) := ⟨pow_ne_zero b (Fact.out : q.Prime).pos.ne'⟩
  let χK : (ZMod (q ^ b))ˣ →* Kˣ := (Units.map (Int.castRingHom K).toMonoidHom).comp χℤ
  have hcomp : ∀ u : (ZMod (q ^ b))ˣ, (χK u : K) = ((χℤ u : ℤ) : K) := fun _ => rfl
  have hχK2 : ∀ u : (ZMod (q ^ b))ˣ, χK u * χK u = 1 := by
    intro u
    have h2 : χℤ u * χℤ u = 1 := Int.units_mul_self _
    have h3 : χK u * χK u = (Units.map (Int.castRingHom K).toMonoidHom) (χℤ u * χℤ u) := by
      rw [map_mul]; rfl
    rw [h3, h2, map_one]
  have hχKne : χK ≠ 1 := by
    intro hK
    apply hχℤne
    ext u
    simp only [MonoidHom.one_apply, Units.val_one]
    have h1 : (χK u : K) = 1 := by rw [hK]; rfl
    have h2 : ((χℤ u : ℤ) : K) = 1 := by rw [← hcomp u]; exact h1
    have h3 : (χℤ u : ℤ) = 1 := by exact_mod_cast h2
    exact_mod_cast h3

  have hM'M : M' ∣ M := hM'div.trans (Nat.div_dvd_of_dvd hNq)
  have hmM : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q ^ b → ℓ ∣ M := fun ℓ hℓp hd => by
    have hℓq : ℓ = q := (Nat.prime_dvd_prime_iff_eq hℓp Fact.out).mp (hℓp.dvd_of_dvd_pow hd)
    rw [hℓq]; exact hqdvdM
  obtain ⟨φ', hφ'⟩ := R1_phiPrime hM'M S chig hchig chih hchihT K φ (q ^ b) hmM χℤ χK hcomp hrel

  refine ⟨q ^ b, ⟨pow_ne_zero b (Fact.out : q.Prime).pos.ne'⟩, ?_, χK, hχK2, hχKne, M', ⟨hM'0⟩,
    h, hhnew, hq2, S ∪ M.primeFactors, chih, hchihT, φ', hφ'⟩
  rcases hbdisj with ⟨hodd, hb⟩ | ⟨hq2', hb⟩
  · exact Or.inl ⟨hodd, by rw [hb, pow_one]⟩
  · exact Or.inr ⟨hq2', by rw [hq2', hb]; norm_num⟩

end
end S_CuspForm_IsNewform_exists_quadraticTwistToExponentOne_of_sq_dvd_of_adelicLift_principalSeries_isUnramified_ratio
end P2MW
export P2MW.S_CuspForm_IsNewform_exists_quadraticTwistToExponentOne_of_sq_dvd_of_adelicLift_principalSeries_isUnramified_ratio (solution)
