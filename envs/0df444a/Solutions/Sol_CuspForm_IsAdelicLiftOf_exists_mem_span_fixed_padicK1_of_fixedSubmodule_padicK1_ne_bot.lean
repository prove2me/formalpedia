-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c38f337f-e832-5d88-ac04-f00973296b86

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_RepTheory_SmoothVectors
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupCompact
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.OpenSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot

set_option autoImplicit false

noncomputable section

namespace TwistprodIsotypy

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
        ext i j : 1
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

private theorem gl2Congr_le_padicK1 (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FLT.SmoothVectors.gl2CongruenceSubgroup p n ≤ _root_.LocalNewvector.padicK1 p n := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hr1 : (p : ℝ) ^ (-(n : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hp1 (by simp)
  intro g hg
  obtain ⟨hg1, hg2⟩ := (FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff p).mp hg

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

section Centre

open IsDedekindDomain NumberField AutomorphicForm

private theorem coe_borelElem_self_zero (q : ℕ) [Fact q.Prime] (u : ℚ_[q]ˣ) :
    (LocalNewvector.borelElem q u u 0 : Matrix (Fin 2) (Fin 2) ℚ_[q]) = Matrix.scalar (Fin 2) (u : ℚ_[q]) := by
  rw [LocalNewvector.coe_borelElem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

private theorem centralGL_eq_borelElem (q : ℕ) [Fact q.Prime] (u : ℚ_[q]ˣ) :
    LocalNewvector.centralGL q u = LocalNewvector.borelElem q u u 0 := by
  apply Units.ext
  rw [coe_borelElem_self_zero]
  show algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q]) (u : ℚ_[q]) = Matrix.scalar (Fin 2) (u : ℚ_[q])
  refine (Matrix.algebraMap_eq_diagonal (u : ℚ_[q])).trans ?_
  exact (Matrix.scalar_apply (n := Fin 2) (u : ℚ_[q])).symm

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

private theorem central_unit_inv {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ) (q : ℕ) [Fact q.Prime] (u : ℚ_[q]ˣ)
    (hu : ‖(u : ℚ_[q])‖ = 1) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (x * AdelicDock.padicToAdelic q (LocalNewvector.centralGL q u)) = Φ x := by
  rw [centralGL_eq_borelElem, AdelicDock.padicToAdelic_apply]
  exact CuspForm.IsAdelicLiftOf.levelZero_inv (NeZero.ne M) hΦg _
    (padicToFinAdelic_borelElem_self_zero_mem q (AdelicDock.ratLevel M) u hu) x

private theorem map_scalar {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) u)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom u) := by
  apply Units.ext
  show f.mapMatrix (Matrix.scalar (Fin 2) (u : A)) = Matrix.scalar (Fin 2) (f (u : A))
  rw [RingHom.mapMatrix_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero f)]

private theorem scalar_mul_comm {A : Type} [CommRing A] (u : Aˣ) (y : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * y = y * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show Matrix.scalar (Fin 2) (u : A) * (y : Matrix (Fin 2) (Fin 2) A)
    = (y : Matrix (Fin 2) (Fin 2) A) * Matrix.scalar (Fin 2) (u : A)
  exact (Matrix.scalar_commute (u : A) (fun r => Commute.all _ r) (y : Matrix (Fin 2) (Fin 2) A)).eq

private def archReal : (default : InfinitePlace ℚ).Completion →+* ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom

private def ratArchHom : AdelicGL2 (𝓞 ℚ) ℚ →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map archReal).comp
    ((AdelicLevel.archComponent ℚ default).comp (AdelicLevel.glArch (𝓞 ℚ) ℚ))

private theorem ratArchGL2_eq (h : AdelicGL2 (𝓞 ℚ) ℚ) : LanglandsTunnell.ratArchGL2 h = ratArchHom h := rfl

private theorem ratArchHom_finEmbed (g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom (AdelicDock.finEmbed (𝓞 ℚ) ℚ g) = 1 := by
  show Matrix.GeneralLinearGroup.map archReal
    (AdelicLevel.archComponent ℚ default (AdelicLevel.glArch (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ g))) = 1
  rw [AdelicDock.glArch_finEmbed, map_one, map_one]

private def qUnit (q : ℕ) [Fact q.Prime] : ℚˣ :=
  Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

private theorem globalPoints_scalar (u : ℚˣ) :
    globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) u)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom u) :=
  map_scalar (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) u

private theorem globalScalar_mul_comm (u : ℚˣ) (y : AdelicGL2 (𝓞 ℚ) ℚ) :
    globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) * y
      = y * globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
  rw [globalPoints_scalar]
  exact scalar_mul_comm _ y

private theorem exists_ratArchHom_globalScalar (q : ℕ) [Fact q.Prime] :
    ∃ r : ℝˣ, (0 : ℝ) < r ∧
      ratArchHom (globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) (qUnit q)))
        = Matrix.GeneralLinearGroup.scalar (Fin 2) r := by
  rw [globalPoints_scalar]
  refine ⟨Units.map archReal.toMonoidHom (Units.map (AdelicLevel.archEval ℚ default).toMonoidHom
    (Units.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).toMonoidHom
      (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (qUnit q)))), ?_, ?_⟩
  · show (0 : ℝ) < archReal (AdelicLevel.archEval ℚ default (AdelicLevel.adeleArch (𝓞 ℚ) ℚ
      (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((q : ℕ) : ℚ))))
    rw [map_natCast, map_natCast, map_natCast, map_natCast]
    exact_mod_cast (Fact.out : q.Prime).pos
  · show Matrix.GeneralLinearGroup.map archReal (Matrix.GeneralLinearGroup.map (AdelicLevel.archEval ℚ default)
      (Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) (Matrix.GeneralLinearGroup.scalar (Fin 2) _))) = _
    rw [map_scalar, map_scalar, map_scalar]

private theorem ratArchHom_central (q : ℕ) [Fact q.Prime] (z : ℚ_[q]ˣ) :
    ratArchHom (AdelicDock.padicToAdelic q (LocalNewvector.centralGL q z)) = 1 := by
  rw [AdelicDock.padicToAdelic_apply, ratArchHom_finEmbed]

private theorem glFin_globalScalar (q : ℕ) [Fact q.Prime] :
    AdelicLevel.glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) (qUnit q)))
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).toMonoidHom
          (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (qUnit q))) := by
  rw [globalPoints_scalar]
  exact map_scalar (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) _

private theorem glFin_central (q : ℕ) [Fact q.Prime] (z : ℚ_[q]ˣ) :
    AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q (LocalNewvector.centralGL q z))
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom z)) := by
  rw [AdelicDock.glFin_padicToAdelic]
  apply Units.ext
  refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
  have hR : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) (AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
        (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom z)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.scalar (Fin 2) (((AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom z) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            FiniteAdeleRing (𝓞 ℚ) ℚ) w) := by
    show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix (Matrix.scalar (Fin 2) _) = _
    rw [RingHom.mapMatrix_apply, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w))]
    rfl
  have hL : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
      ((AdelicDock.padicToFinAdelic q (LocalNewvector.centralGL q z) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = ((AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicDock.padicToFinAdelic q (LocalNewvector.centralGL q z)) :
          GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) := rfl
  rw [hL, hR]
  by_cases hw : w = AdelicDock.padicPlace q
  · subst hw
    rw [AdelicDock.finComponent_padicToFinAdelic_self, AdelicLevel.localUnit_apply_self]
    show (AdelicDock.padicRingEquiv q).toRingHom.mapMatrix
        ((LocalNewvector.centralGL q z : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q])
      = Matrix.scalar (Fin 2) ((AdelicDock.padicRingEquiv q).toRingHom (z : ℚ_[q]))
    rw [centralGL_eq_borelElem, coe_borelElem_self_zero, RingHom.mapMatrix_apply, Matrix.scalar_apply,
      Matrix.scalar_apply, Matrix.diagonal_map (map_zero (AdelicDock.padicRingEquiv q).toRingHom)]
  · rw [AdelicDock.finComponent_padicToFinAdelic_of_ne q _ hw, AdelicLevel.localUnit_apply_of_ne _ _ _ _ hw,
      Units.val_one, map_one]

private theorem scalar_mem_finiteLevelZero (N : Ideal (𝓞 ℚ)) (z : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 ℚ), (z : FiniteAdeleRing (𝓞 ℚ) ℚ) w ∈ w.adicCompletionIntegers ℚ)
    (hz' : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((z⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w
      ∈ w.adicCompletionIntegers ℚ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) z ∈ AdelicLevel.finiteLevelZero (𝓞 ℚ) ℚ N := by
  have key : ∀ y : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∀ w : HeightOneSpectrum (𝓞 ℚ), (y : FiniteAdeleRing (𝓞 ℚ) ℚ) w ∈ w.adicCompletionIntegers ℚ) →
      AdelicLevel.IsLevelZeroMatrix (𝓞 ℚ) ℚ N
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) y : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    intro y hy
    refine ⟨fun i j => ?_, ?_⟩
    · show Matrix.scalar (Fin 2) (y : FiniteAdeleRing (𝓞 ℚ) ℚ) i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · exact hy
      · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · show Matrix.scalar (Fin 2) (y : FiniteAdeleRing (𝓞 ℚ) ℚ) 1 0 ∈ AdelicLevel.idealBall (𝓞 ℚ) ℚ N
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
      exact AdelicLevel.zero_mem_idealBall N
  rw [AdelicLevel.mem_finiteLevelZero_iff, ← map_inv]
  exact ⟨key z hz, key z⁻¹ hz'⟩

private theorem natGenerator_ne (q : ℕ) [Fact q.Prime] {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ AdelicDock.padicPlace q) : Rat.HeightOneSpectrum.natGenerator w ≠ q := by
  intro h
  apply hw
  show w = (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, Fact.out⟩
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext h

private theorem natCast_not_mem_asIdeal (q : ℕ) [Fact q.Prime] {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ AdelicDock.padicPlace q) : ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  intro hmem
  have hdvd : Rat.HeightOneSpectrum.natGenerator w ∣ q := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have h := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem
    rwa [map_natCast] at h
  exact natGenerator_ne q hw
    ((Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) (Fact.out : q.Prime)).mp hdvd)

private theorem natCast_eq_algebraMap (q : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((q : ℕ) : w.adicCompletion ℚ) = algebraMap ℚ (w.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ ((q : ℕ) : 𝓞 ℚ)) := by
  rw [map_natCast, map_natCast]

private theorem natCast_mem_integers (q : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((q : ℕ) : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  rw [natCast_eq_algebraMap]
  exact AdelicLevel.algebraMap_mem_adicCompletionIntegers w _

private theorem natCast_inv_mem_integers (q : ℕ) [Fact q.Prime] {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ AdelicDock.padicPlace q) :
    ((q : ℕ) : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  have hval : Valued.v ((q : ℕ) : w.adicCompletion ℚ) = 1 := by
    rw [natCast_eq_algebraMap, AdelicLevel.valued_algebraMap]
    refine le_antisymm (w.intValuation_le_one _) (not_lt.mp ?_)
    rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact natCast_not_mem_asIdeal q hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval]
  exact inv_one.le

private theorem natCast_ne_zero' (q : ℕ) [Fact q.Prime] (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((q : ℕ) : w.adicCompletion ℚ) ≠ 0 := by
  haveI : CharZero (w.adicCompletion ℚ) := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  exact Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

private def qFin (q : ℕ) [Fact q.Prime] : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).toMonoidHom
    (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (qUnit q))

private theorem qFin_apply (q : ℕ) [Fact q.Prime] (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((qFin q : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w = ((q : ℕ) : w.adicCompletion ℚ) := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w (AdelicLevel.adeleFin (𝓞 ℚ) ℚ
    (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((q : ℕ) : ℚ))) = _
  rw [map_natCast, map_natCast, map_natCast]

private theorem qFin_inv_apply (q : ℕ) [Fact q.Prime] (w : HeightOneSpectrum (𝓞 ℚ)) :
    (((qFin q)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w = ((q : ℕ) : w.adicCompletion ℚ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← qFin_apply q w]
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w (((qFin q)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
    * AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w ((qFin q : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1
  rw [← map_mul, Units.inv_mul, map_one]

private def piFin (q : ℕ) [Fact q.Prime] (ϖ : ℚ_[q]ˣ) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom ϖ)

private theorem piFin_apply_self (q : ℕ) [Fact q.Prime] (ϖ : ℚ_[q]ˣ) (hϖ : (ϖ : ℚ_[q]) = q) :
    ((piFin q ϖ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) (AdelicDock.padicPlace q)
      = ((q : ℕ) : (AdelicDock.padicPlace q).adicCompletion ℚ) := by
  rw [piFin, AdelicLevel.localUnit_apply_self]
  show (AdelicDock.padicRingEquiv q) (ϖ : ℚ_[q]) = _
  rw [hϖ, map_natCast]

private theorem piFin_apply_of_ne (q : ℕ) [Fact q.Prime] (ϖ : ℚ_[q]ˣ) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ AdelicDock.padicPlace q) :
    ((piFin q ϖ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1 := by
  rw [piFin, AdelicLevel.localUnit_apply_of_ne _ _ _ _ hw]

private theorem piFin_inv_apply_self (q : ℕ) [Fact q.Prime] (ϖ : ℚ_[q]ˣ) (hϖ : (ϖ : ℚ_[q]) = q) :
    (((piFin q ϖ)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) (AdelicDock.padicPlace q)
      = ((q : ℕ) : (AdelicDock.padicPlace q).adicCompletion ℚ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← piFin_apply_self q ϖ hϖ]
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
      (((piFin q ϖ)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
    * AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
      ((piFin q ϖ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1
  rw [← map_mul, Units.inv_mul, map_one]

private theorem piFin_inv_apply_of_ne (q : ℕ) [Fact q.Prime] (ϖ : ℚ_[q]ˣ) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ AdelicDock.padicPlace q) :
    (((piFin q ϖ)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1 := by
  have h : ((piFin q ϖ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w
      * (((piFin q ϖ)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1 := by
    show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w ((piFin q ϖ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      * AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w (((piFin q ϖ)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1
    rw [← map_mul, Units.mul_inv, map_one]
  rwa [piFin_apply_of_ne q ϖ hw, one_mul] at h

private theorem compensator_mem (N : Ideal (𝓞 ℚ)) (q : ℕ) [Fact q.Prime] (ϖ : ℚ_[q]ˣ) (hϖ : (ϖ : ℚ_[q]) = q) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) ((qFin q)⁻¹ * piFin q ϖ) ∈ AdelicLevel.finiteLevelZero (𝓞 ℚ) ℚ N := by
  refine scalar_mem_finiteLevelZero N _ (fun w => ?_) (fun w => ?_)
  · show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w ((((qFin q)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      * ((piFin q ϖ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ w.adicCompletionIntegers ℚ
    rw [map_mul]
    show (((qFin q)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w
      * ((piFin q ϖ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w ∈ w.adicCompletionIntegers ℚ
    rw [qFin_inv_apply]
    by_cases hw : w = AdelicDock.padicPlace q
    · subst hw
      rw [piFin_apply_self q ϖ hϖ, inv_mul_cancel₀ (natCast_ne_zero' q _)]
      exact one_mem _
    · rw [piFin_apply_of_ne q ϖ hw, mul_one]
      exact natCast_inv_mem_integers q hw
  · rw [mul_inv_rev, inv_inv]
    show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w ((((piFin q ϖ)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      * ((qFin q : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ w.adicCompletionIntegers ℚ
    rw [map_mul]
    show (((piFin q ϖ)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w
      * ((qFin q : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w ∈ w.adicCompletionIntegers ℚ
    rw [qFin_apply]
    by_cases hw : w = AdelicDock.padicPlace q
    · subst hw
      rw [piFin_inv_apply_self q ϖ hϖ, inv_mul_cancel₀ (natCast_ne_zero' q _)]
      exact one_mem _
    · rw [piFin_inv_apply_of_ne q ϖ hw, one_mul]
      exact natCast_mem_integers q w

private theorem glFin_compensator (q : ℕ) [Fact q.Prime] (ϖ : ℚ_[q]ˣ) :
    AdelicLevel.glFin (𝓞 ℚ) ℚ ((globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) (qUnit q)))⁻¹
        * AdelicDock.padicToAdelic q (LocalNewvector.centralGL q ϖ))
      = Matrix.GeneralLinearGroup.scalar (Fin 2) ((qFin q)⁻¹ * piFin q ϖ) := by
  rw [map_mul, map_inv, glFin_globalScalar, glFin_central, map_mul, map_inv]
  rfl

open scoped ModularForm in
private theorem slash_scalar_apply (F : UpperHalfPlane → ℂ) (r : ℝˣ) (hr : (0 : ℝ) < r) (τ : UpperHalfPlane) :
    (F ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.scalar (Fin 2) r) τ = F τ := by
  have hdet : (0 : ℝ) < (Matrix.GeneralLinearGroup.scalar (Fin 2) r).det.val := by
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val]
    positivity
  have hr' : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [ModularForm.slash_apply, UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar, abs_of_pos hdet,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val]
  simp only [UpperHalfPlane.σ, if_pos hdet, ContinuousAlgEquiv.refl_apply]
  rw [show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, zpow_neg, zpow_two]
  push_cast
  field_simp

private theorem central_uniformizer_of_levelOne {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ) (q : ℕ) [Fact q.Prime] (ϖ : ℚ_[q]ˣ)
    (hϖ : (ϖ : ℚ_[q]) = q) (y : AdelicGL2 (𝓞 ℚ) ℚ)
    (hy : AdelicLevel.glFin (𝓞 ℚ) ℚ y ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (hyArch : ratArchHom y ∈ Matrix.GLPos (Fin 2) ℝ) :
    Φ (y * AdelicDock.padicToAdelic q (LocalNewvector.centralGL q ϖ)) = Φ y := by
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : AdelicGL2 (𝓞 ℚ) ℚ,
      Γ = globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) (qUnit q)) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : AdelicGL2 (𝓞 ℚ) ℚ, s = AdelicDock.padicToAdelic q (LocalNewvector.centralGL q ϖ) :=
    ⟨_, rfl⟩
  rw [← hs]
  have hΓcomm : Γ * y = y * Γ := by
    rw [hΓ]
    exact globalScalar_mul_comm _ y
  obtain ⟨r, hr, hΓr⟩ : ∃ r : ℝˣ, (0 : ℝ) < r ∧ ratArchHom Γ = Matrix.GeneralLinearGroup.scalar (Fin 2) r := by
    rw [hΓ]
    exact exists_ratArchHom_globalScalar q
  have hsArch : ratArchHom s = 1 := by
    rw [hs]
    exact ratArchHom_central q ϖ
  have hcfin : AdelicLevel.glFin (𝓞 ℚ) ℚ (Γ⁻¹ * s)
      ∈ AdelicLevel.finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by
    rw [hΓ, hs, glFin_compensator]
    exact compensator_mem _ q ϖ hϖ

  have h1 : Φ (y * s) = Φ (y * (Γ⁻¹ * s)) := by
    have e1 : Γ * (y * (Γ⁻¹ * s)) = y * s := by
      rw [← mul_assoc, hΓcomm, mul_assoc, mul_inv_cancel_left]
    have h := hΦg.left_inv (Matrix.GeneralLinearGroup.scalar (Fin 2) (qUnit q)) (y * (Γ⁻¹ * s))
    rw [← hΓ, e1] at h
    exact h

  have hku : AdelicLevel.glFin (𝓞 ℚ) ℚ y * AdelicLevel.glFin (𝓞 ℚ) ℚ (Γ⁻¹ * s)
      ∈ AdelicLevel.finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) :=
    mul_mem (AdelicLevel.finiteLevelOne_le_finiteLevelZero (𝓞 ℚ) ℚ _ hy) hcfin
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : AdelicGL2 (𝓞 ℚ) ℚ, z₁ = y * (Γ⁻¹ * s) *
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicLevel.glFin (𝓞 ℚ) ℚ y * AdelicLevel.glFin (𝓞 ℚ) ℚ (Γ⁻¹ * s)))⁻¹ :=
    ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z₂ : AdelicGL2 (𝓞 ℚ) ℚ,
      z₂ = y * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicLevel.glFin (𝓞 ℚ) ℚ y))⁻¹ := ⟨_, rfl⟩
  have h2 : Φ (y * (Γ⁻¹ * s)) = Φ z₁ := by
    have h := CuspForm.IsAdelicLiftOf.levelZero_inv (NeZero.ne M) hΦg _ hku z₁
    rw [hz₁, inv_mul_cancel_right] at h
    rw [hz₁]
    exact h
  have h3 : Φ y = Φ z₂ := by
    have h := hΦg.level_inv _ hy z₂
    rw [hz₂, inv_mul_cancel_right] at h
    rw [hz₂]
    exact h
  have hz₁fin : AdelicLevel.glFin (𝓞 ℚ) ℚ z₁ = 1 := by
    rw [hz₁, map_mul, map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel]
  have hz₂fin : AdelicLevel.glFin (𝓞 ℚ) ℚ z₂ = 1 := by
    rw [hz₂, map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel]

  have hz₁Arch : ratArchHom z₁ = ratArchHom y * (Matrix.GeneralLinearGroup.scalar (Fin 2) r)⁻¹ := by
    rw [hz₁]
    simp only [map_mul, map_inv, ratArchHom_finEmbed, inv_one, mul_one, hΓr, hsArch]
  have hz₂Arch : ratArchHom z₂ = ratArchHom y := by
    rw [hz₂, map_mul, map_inv, ratArchHom_finEmbed, inv_one, mul_one]
  have hrpos : Matrix.GeneralLinearGroup.scalar (Fin 2) r ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val]
    positivity
  have hz₁pos : LanglandsTunnell.ratArchGL2 z₁ ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [ratArchGL2_eq, hz₁Arch]
    exact mul_mem hyArch (inv_mem hrpos)
  have hz₂pos : LanglandsTunnell.ratArchGL2 z₂ ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [ratArchGL2_eq, hz₂Arch]
    exact hyArch
  have hrinv : (0 : ℝ) < ((r⁻¹ : ℝˣ) : ℝ) := by
    rw [Units.val_inv_eq_inv_val]
    positivity

  rw [h1, h2, h3, hΦg.2.2 z₁ hz₁fin hz₁pos, hΦg.2.2 z₂ hz₂fin hz₂pos, ratArchGL2_eq, ratArchGL2_eq, hz₁Arch, hz₂Arch,
    ← map_inv, SlashAction.slash_mul, slash_scalar_apply _ r⁻¹ hrinv]

private theorem hole_central_uniformizer {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ) (q : ℕ) [Fact q.Prime] (ϖ : ℚ_[q]ˣ)
    (hϖ : (ϖ : ℚ_[q]) = q) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (x * AdelicDock.padicToAdelic q (LocalNewvector.centralGL q ϖ)) = Φ x := by
  obtain ⟨δ, hδ, hpos⟩ :=
    AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat (AdelicDock.ratLevel_ne_bot (NeZero.ne M)) x
  have hy : AdelicLevel.glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ * x)
      ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := hδ
  have hyArch : LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ δ * x) ∈ Matrix.GLPos (Fin 2) ℝ :=
    hpos default (IsTotallyReal.isReal default)
  rw [ratArchGL2_eq] at hyArch
  have h := central_uniformizer_of_levelOne Φ hΦg q ϖ hϖ _ hy hyArch
  rwa [mul_assoc, hΦg.left_inv, hΦg.left_inv] at h

private theorem central_uniformizer_pow_inv {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ) (q : ℕ) [Fact q.Prime] (ϖ : ℚ_[q]ˣ)
    (hϖ : (ϖ : ℚ_[q]) = q) (n : ℕ) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (x * AdelicDock.padicToAdelic q (LocalNewvector.centralGL q (ϖ ^ n))) = Φ x := by
  induction n generalizing x with
  | zero => rw [pow_zero, map_one, map_one, mul_one]
  | succ n ih =>
    rw [pow_succ, map_mul, map_mul, ← mul_assoc, hole_central_uniformizer Φ hΦg q ϖ hϖ, ih]

private theorem central_inv_of_norm_le_one {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ) (q : ℕ) [Fact q.Prime] (z : ℚ_[q]ˣ)
    (hz : ‖(z : ℚ_[q])‖ ≤ 1) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (x * AdelicDock.padicToAdelic q (LocalNewvector.centralGL q z)) = Φ x := by
  set y : ℤ_[q] := ⟨(z : ℚ_[q]), hz⟩ with hy
  have hy0 : y ≠ 0 := fun h => z.ne_zero (congrArg Subtype.val h)
  have hspec := PadicInt.unitCoeff_spec hy0
  set u : ℤ_[q]ˣ := PadicInt.unitCoeff hy0 with hu_def
  set n : ℕ := y.valuation with hn_def
  have hq0 : (q : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hzeq : z = Units.map PadicInt.Coe.ringHom.toMonoidHom u * (Units.mk0 (q : ℚ_[q]) hq0) ^ n := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    show (z : ℚ_[q]) = ((u : ℤ_[q]) : ℚ_[q]) * (q : ℚ_[q]) ^ n
    have h1 : ((y : ℤ_[q]) : ℚ_[q]) = (z : ℚ_[q]) := rfl
    rw [← h1, hspec]
    first
      | (push_cast; done)
      | (push_cast; ring)
  have hu1 : ‖((Units.map PadicInt.Coe.ringHom.toMonoidHom u : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by
    show ‖((u : ℤ_[q]) : ℚ_[q])‖ = 1
    rw [← PadicInt.norm_def]
    exact PadicInt.norm_units u
  rw [hzeq, map_mul, map_mul, ← mul_assoc,
    central_uniformizer_pow_inv Φ hΦg q (Units.mk0 (q : ℚ_[q]) hq0) (Units.val_mk0 hq0) n,
    central_unit_inv Φ hΦg q _ hu1]

private theorem hole_central_lift {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ) (q : ℕ) [Fact q.Prime] (z : ℚ_[q]ˣ)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (x * AdelicDock.padicToAdelic q (LocalNewvector.centralGL q z)) = Φ x := by
  by_cases hz : ‖(z : ℚ_[q])‖ ≤ 1
  · exact central_inv_of_norm_le_one Φ hΦg q z hz x
  · have hz' : ‖((z⁻¹ : ℚ_[q]ˣ) : ℚ_[q])‖ ≤ 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hz))
    have h := central_inv_of_norm_le_one Φ hΦg q z⁻¹ hz'
      (x * AdelicDock.padicToAdelic q (LocalNewvector.centralGL q z))
    rw [mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, mul_one] at h
    exact h.symm

end Centre

open NumberField AutomorphicForm LocalNewvector in

private theorem central_trivial {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] (z : ℚ_[q]ˣ) (v : LocalNewvector.AdelicSpan Φ) :
    LocalNewvector.centralGL q z • v = v := by
  have hFn : ∀ x, Φ (x * AdelicDock.padicToAdelic q (centralGL q z)) = Φ x :=
    fun x => hole_central_lift Φ hΦg q z x
  set cz : AdelicGL2 (𝓞 ℚ) ℚ := AdelicDock.padicToAdelic q (centralGL q z) with hcz
  rw [AdelicSpan.padic_smul_def, ← hcz]
  obtain ⟨ψ, hψ⟩ := v
  apply AdelicSpan.ext
  rw [AdelicSpan.toFn_smul]
  show cz • ψ = ψ
  refine Submodule.span_induction (p := fun ψ _ => cz • ψ = ψ)
    ?_ (smul_zero cz)
    (fun x y _ _ hx hy => ?_)
    (fun c x _ hx => ?_) hψ
  · intro ψ₀ hψ₀
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

section Main

variable {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
  (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (q : ℕ) [Fact q.Prime]

private abbrev qSpan : Submodule ℂ (_root_.LocalNewvector.AdelicSpan Φ) :=
  Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • _root_.LocalNewvector.AdelicSpan.self Φ)

private theorem exists_commute (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    ∃ g₀ : GL (Fin 2) ℚ_[q], ∀ k : GL (Fin 2) ℚ_[q],
      x * (AdelicDock.padicToAdelic q g₀)⁻¹ * AdelicDock.padicToAdelic q k =
        AdelicDock.padicToAdelic q k * (x * (AdelicDock.padicToAdelic q g₀)⁻¹) := by
  obtain ⟨g₀, h⟩ := aux_conj_padicToAdelic q x
  refine ⟨g₀, fun k => ?_⟩
  have h1 := h (g₀⁻¹ * k * g₀)
  have e : g₀ * (g₀⁻¹ * k * g₀) * g₀⁻¹ = k := by group
  rw [e] at h1
  simp only [map_mul, map_inv] at h1
  calc x * (AdelicDock.padicToAdelic q g₀)⁻¹ * AdelicDock.padicToAdelic q k
      = x * ((AdelicDock.padicToAdelic q g₀)⁻¹ * AdelicDock.padicToAdelic q k *
          AdelicDock.padicToAdelic q g₀) * (AdelicDock.padicToAdelic q g₀)⁻¹ := by group
    _ = AdelicDock.padicToAdelic q k * x * (AdelicDock.padicToAdelic q g₀)⁻¹ := by rw [← h1]
    _ = AdelicDock.padicToAdelic q k * (x * (AdelicDock.padicToAdelic q g₀)⁻¹) := by group

private theorem smul_mem_qSpan (x : GL (Fin 2) ℚ_[q]) {w : _root_.LocalNewvector.AdelicSpan Φ}
    (hw : w ∈ qSpan Φ q) : x • w ∈ qSpan Φ q := by
  refine Submodule.span_induction (p := fun w _ => x • w ∈ qSpan Φ q) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨x', rfl⟩
    exact Submodule.subset_span ⟨x * x', by simp only [mul_smul]⟩
  · simp only [smul_zero]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [smul_comm]; exact Submodule.smul_mem _ c ha

private theorem mem_span_orbit (ψ : _root_.LocalNewvector.AdelicSpan Φ) :
    ψ ∈ Submodule.span ℂ (Set.range fun h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ =>
      h • _root_.LocalNewvector.AdelicSpan.self Φ) := by
  let incl : _root_.LocalNewvector.AdelicSpan Φ →ₗ[ℂ] _root_.LocalNewvector.AdelicFnCarrier ℚ :=
    { toFun := _root_.LocalNewvector.AdelicSpan.toFn Φ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective incl := by
    intro a b h
    apply _root_.LocalNewvector.AdelicSpan.ext
    exact h
  set S := Submodule.span ℂ (Set.range fun h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ =>
      h • _root_.LocalNewvector.AdelicSpan.self Φ) with hS
  have himage : _root_.LocalNewvector.AdelicSpanSubmodule Φ ≤ Submodule.map incl S := by
    rw [hS, Submodule.map_span]
    unfold _root_.LocalNewvector.AdelicSpanSubmodule
    apply Submodule.span_mono
    rintro ψ' ⟨h, rfl⟩
    refine ⟨h • _root_.LocalNewvector.AdelicSpan.self Φ, ⟨h, rfl⟩, ?_⟩
    show _root_.LocalNewvector.AdelicSpan.toFn Φ (h • _root_.LocalNewvector.AdelicSpan.self Φ) = _
    rw [_root_.LocalNewvector.AdelicSpan.toFn_smul, _root_.LocalNewvector.AdelicSpan.toFn_self]
  have hψ : incl ψ ∈ Submodule.map incl S :=
    himage (ψ : _root_.LocalNewvector.AdelicSpanSubmodule Φ).2
  obtain ⟨s, hs, hsi⟩ := Submodule.mem_map.mp hψ
  exact hinj hsi ▸ hs

private theorem sum_smul_comm (c : ℂ)
    (l : List (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ × _root_.LocalNewvector.AdelicSpan Φ)) :
    ((l.map fun p => (p.1, c • p.2)).map fun p => p.1 • p.2).sum = c • (l.map fun p => p.1 • p.2).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
    simp only [List.map_cons, List.sum_cons, smul_add, ih]
    rw [smul_comm p.1 c p.2]

private theorem decomp (ψ : _root_.LocalNewvector.AdelicSpan Φ) :
    ∃ l : List (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ × _root_.LocalNewvector.AdelicSpan Φ),
      (∀ p ∈ l, (∀ k : GL (Fin 2) ℚ_[q],
          p.1 * AdelicDock.padicToAdelic q k = AdelicDock.padicToAdelic q k * p.1) ∧ p.2 ∈ qSpan Φ q) ∧
      (l.map fun p => p.1 • p.2).sum = ψ := by
  refine Submodule.span_induction
    (p := fun ψ _ => ∃ l : List (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ ×
        _root_.LocalNewvector.AdelicSpan Φ),
      (∀ p ∈ l, (∀ k : GL (Fin 2) ℚ_[q],
          p.1 * AdelicDock.padicToAdelic q k = AdelicDock.padicToAdelic q k * p.1) ∧ p.2 ∈ qSpan Φ q) ∧
      (l.map fun p => p.1 • p.2).sum = ψ) ?_ ?_ ?_ ?_ (mem_span_orbit Φ ψ)
  · rintro _ ⟨h, rfl⟩
    obtain ⟨g₀, hcomm⟩ := exists_commute q h
    refine ⟨[(h * (AdelicDock.padicToAdelic q g₀)⁻¹, g₀ • _root_.LocalNewvector.AdelicSpan.self Φ)], ?_, ?_⟩
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact ⟨hcomm, Submodule.subset_span ⟨g₀, rfl⟩⟩
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [_root_.LocalNewvector.AdelicSpan.padic_smul_def, ← mul_smul, inv_mul_cancel_right]
  · exact ⟨[], fun p hp => absurd hp List.not_mem_nil, rfl⟩
  · rintro a b _ _ ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩
    refine ⟨l₁ ++ l₂, fun p hp => ?_, by rw [List.map_append, List.sum_append]⟩
    rcases List.mem_append.mp hp with hp | hp
    exacts [h₁ p hp, h₂ p hp]
  · rintro c a _ ⟨l, hl, rfl⟩
    refine ⟨l.map fun p => (p.1, c • p.2), fun p hp => ?_, sum_smul_comm Φ c l⟩
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
    exact ⟨(hl p' hp').1, Submodule.smul_mem _ c (hl p' hp').2⟩

private theorem exists_level (hΦg : g.IsAdelicLiftOf Φ)
    (l : List (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ × _root_.LocalNewvector.AdelicSpan Φ)) :
    ∃ n : ℕ, ∀ p ∈ l, ∀ γ ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q n, γ • p.2 = p.2 := by
  have key : ∃ U : Subgroup (GL (Fin 2) ℚ_[q]), IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧
      ∀ p ∈ l, ∀ u ∈ U, u • p.2 = p.2 := by
    induction l with
    | nil =>
      exact ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun p hp => absurd hp List.not_mem_nil⟩
    | cons p t ih =>
      obtain ⟨U₁, hU₁o, hU₁⟩ := ih
      obtain ⟨U₂, hU₂o, hU₂⟩ := aux_span_smooth Φ hΦg q p.2 Submodule.mem_top
      refine ⟨U₁ ⊓ U₂, by rw [Subgroup.coe_inf]; exact hU₁o.inter hU₂o, fun p' hp' u hu => ?_⟩
      obtain ⟨h₁, h₂⟩ := Subgroup.mem_inf.mp hu
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact hU₂ u h₂
      · exact hU₁ p' hp' u h₁
  obtain ⟨U, hUo, hU⟩ := key
  obtain ⟨n, hn⟩ := FLT.SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one q
    (hUo.mem_nhds (SetLike.mem_coe.mpr (one_mem U)))
  exact ⟨n, fun p hp γ hγ => hU p hp γ (hn hγ)⟩

private theorem main (hΦg : g.IsAdelicLiftOf Φ) (a : ℕ)
    (hfix : _root_.LocalNewvector.fixedSubmodule (_root_.LocalNewvector.padicK1 q a)
      (_root_.LocalNewvector.AdelicSpan Φ) ≠ ⊥) :
    ∃ y : _root_.LocalNewvector.AdelicSpan Φ,
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] => x • _root_.LocalNewvector.AdelicSpan.self Φ) ∧
      y ≠ 0 ∧
      y ∈ _root_.LocalNewvector.fixedSubmodule (_root_.LocalNewvector.padicK1 q a)
        (_root_.LocalNewvector.AdelicSpan Φ) ∧
      ∀ z : ℚ_[q]ˣ, _root_.LocalNewvector.centralGL q z • y = y := by
  classical
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hfix
  have hvU : ∀ k ∈ _root_.LocalNewvector.padicK1 q a, k • v = v :=
    _root_.LocalNewvector.mem_fixedSubmodule_iff.mp hv
  obtain ⟨l, hl, hsum⟩ := decomp Φ q v
  obtain ⟨n, hn⟩ := exists_level Φ q hΦg l

  set U : Subgroup (GL (Fin 2) ℚ_[q]) := _root_.LocalNewvector.padicK1 q a with hUdef
  set Γ : Subgroup (GL (Fin 2) ℚ_[q]) := FLT.SmoothVectors.gl2CongruenceSubgroup q (n + a) with hΓdef
  have hΓn : Γ ≤ FLT.SmoothVectors.gl2CongruenceSubgroup q n :=
    FLT.SmoothVectors.gl2CongruenceSubgroup_antitone q (Nat.le_add_right n a)
  have hΓU : Γ ≤ U :=
    (FLT.SmoothVectors.gl2CongruenceSubgroup_antitone q (Nat.le_add_left a n)).trans (gl2Congr_le_padicK1 q a)
  have hΓw : ∀ p ∈ l, ∀ γ ∈ Γ, γ • p.2 = p.2 := fun p hp γ hγ => hn p hp γ (hΓn hγ)
  set H : Subgroup U := Γ.subgroupOf U with hHdef

  haveI hUc : CompactSpace U := by
    refine isCompact_iff_compactSpace.mp ?_
    refine (FLT.SpectralSide.isCompact_coe_integralSubgroup_padic q).of_isClosed_subset
      (U.isClosed_of_isOpen (isOpen_padicK1 q a)) ?_
    intro x hx
    exact _root_.LocalNewvector.congruenceK1_le_integralSubgroup ((q : ℤ_[q])) a hx
  have hHo : IsOpen (H : Set U) := by
    rw [hHdef, Subgroup.coe_subgroupOf, Subgroup.coe_subtype]
    exact (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup q (n + a)).preimage continuous_subtype_val
  haveI : Finite (U ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (U ⧸ H) := Fintype.ofFinite _
  letI instQuotAct : MulAction U (U ⧸ H) := MulAction.quotient U H

  let P : _root_.LocalNewvector.AdelicSpan Φ →+ _root_.LocalNewvector.AdelicSpan Φ :=
    ∑ c : U ⧸ H, DistribSMul.toAddMonoidHom (_root_.LocalNewvector.AdelicSpan Φ)
      ((Quotient.out c : U) : GL (Fin 2) ℚ_[q])
  have P_apply : ∀ u : _root_.LocalNewvector.AdelicSpan Φ,
      P u = ∑ c : U ⧸ H, ((Quotient.out c : U) : GL (Fin 2) ℚ_[q]) • u := by
    intro u
    simp only [P, AddMonoidHom.finsetSum_apply, DistribSMul.toAddMonoidHom_apply]

  have P_fixed : ∀ u : _root_.LocalNewvector.AdelicSpan Φ, (∀ γ ∈ Γ, γ • u = u) →
      ∀ k ∈ U, k • P u = P u := by
    intro u hu k hk
    rw [P_apply, Finset.smul_sum]

    have step : ∀ c : U ⧸ H,
        k • (((Quotient.out c : U) : GL (Fin 2) ℚ_[q]) • u) =
          ((Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U) : GL (Fin 2) ℚ_[q]) • u := by
      intro c
      have hrel : (Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U)⁻¹ * ((⟨k, hk⟩ : U) * Quotient.out c) ∈ H := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      have hγ : (((Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U) : GL (Fin 2) ℚ_[q]))⁻¹ *
          (k * ((Quotient.out c : U) : GL (Fin 2) ℚ_[q])) ∈ Γ := by
        have h2 := Subgroup.mem_subgroupOf.mp hrel
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] using h2
      calc k • (((Quotient.out c : U) : GL (Fin 2) ℚ_[q]) • u)
          = (k * ((Quotient.out c : U) : GL (Fin 2) ℚ_[q])) • u := by rw [← mul_smul]
        _ = (((Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U) : GL (Fin 2) ℚ_[q]) *
              ((((Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U) : GL (Fin 2) ℚ_[q]))⁻¹ *
                (k * ((Quotient.out c : U) : GL (Fin 2) ℚ_[q])))) • u := by rw [mul_inv_cancel_left]
        _ = ((Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U) : GL (Fin 2) ℚ_[q]) • u := by rw [mul_smul, hu _ hγ]
    rw [Finset.sum_congr rfl fun c _ => step c]
    exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : U)) _ _ fun c => rfl

  have P_self : P v = (Fintype.card (U ⧸ H)) • v := by
    rw [P_apply]
    have : ∀ c : U ⧸ H, ((Quotient.out c : U) : GL (Fin 2) ℚ_[q]) • v = v :=
      fun c => hvU _ (Quotient.out c : U).2
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_const, Finset.card_univ]

  have P_comm : ∀ (b : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
      (w : _root_.LocalNewvector.AdelicSpan Φ),
      (∀ k : GL (Fin 2) ℚ_[q], b * AdelicDock.padicToAdelic q k = AdelicDock.padicToAdelic q k * b) →
      P (b • w) = b • P w := by
    intro b w hb
    rw [P_apply, P_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [_root_.LocalNewvector.AdelicSpan.padic_smul_def, _root_.LocalNewvector.AdelicSpan.padic_smul_def,
      ← mul_smul, ← hb, mul_smul]

  have P_qSpan : ∀ w ∈ qSpan Φ q, P w ∈ qSpan Φ q := by
    intro w hw
    rw [P_apply]
    exact Submodule.sum_mem _ fun c _ => smul_mem_qSpan Φ q _ hw

  have hPv : P v ≠ 0 := by
    rw [P_self, ← Nat.cast_smul_eq_nsmul ℂ]
    intro h0
    apply hv0
    have hN : (Fintype.card (U ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    calc v = ((Fintype.card (U ⧸ H) : ℂ)⁻¹ * (Fintype.card (U ⧸ H) : ℂ)) • v := by
            rw [inv_mul_cancel₀ hN, one_smul]
      _ = 0 := by rw [mul_smul, h0, smul_zero]
  have hPsum : P v = (l.map fun p => p.1 • P p.2).sum := by
    rw [← hsum, map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    simp only [Function.comp_apply]
    exact P_comm p.1 p.2 (hl p hp).1

  have hex : ∃ p ∈ l, P p.2 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hPv
    rw [hPsum]
    have : (l.map fun p => p.1 • P p.2) = l.map fun _ => (0 : _root_.LocalNewvector.AdelicSpan Φ) := by
      refine List.map_congr_left fun p hp => ?_
      rw [hall p hp, smul_zero]
    rw [this, List.map_const', List.sum_replicate, smul_zero]
  obtain ⟨p, hp, hPp⟩ := hex
  refine ⟨P p.2, P_qSpan p.2 (hl p hp).2, hPp, ?_, fun z => central_trivial Φ hΦg q z _⟩
  exact _root_.LocalNewvector.mem_fixedSubmodule_iff.mpr (P_fixed p.2 (hΓw p hp))

end Main

end TwistprodIsotypy

theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] (a : ℕ)
    (hfix : LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.AdelicSpan Φ) ≠ ⊥) :
    ∃ y : LocalNewvector.AdelicSpan Φ,
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.AdelicSpan Φ) ∧
      ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y = y :=
  TwistprodIsotypy.main Φ q hΦg a hfix

end
end S_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot (solution)
