-- Prove2me | solution 1 for CerednikDrinfeld.QM.forall_trace_eq_intCast_of_isFormalCoordinates_of_isSpecial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/667f57d8-6926-5820-80cd-bea6e633312c

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_forall_trace_eq_intCast_of_isFormalCoordinates_of_isSpecial

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped Quaternion TensorProduct NumberField

namespace Q4Asm

open MvFormalGroup (linearPart)

section frob
variable {r : ℕ} [Fact r.Prime]

theorem frobenius_frobenius (a : Zp2 r) : WittVector.frobenius (WittVector.frobenius a) = a := by
  haveI : Fintype (GaloisField r 2) := Fintype.ofFinite _
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul]
  have hcard : Fintype.card (GaloisField r 2) = r * r := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card r 2 two_ne_zero, pow_two]
  rw [← hcard]
  exact FiniteField.pow_card _

end frob

section alg
variable {r : ℕ} [Fact r.Prime] {k : Type} [Field k]

theorem trace_mulVecLin (M : Matrix (Fin 2) (Fin 2) k) :
    LinearMap.trace k (Fin 2 → k) M.mulVecLin = M.trace := by
  rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem trace_linearPart_eq (j : Zp2 r →+* k) (X : FormalODModule r k) (hX : X.IsSpecial j) (α β : Zp2 r) :
    Matrix.trace (linearPart (Series.addVia X.F (X.act α) ((X.act β).comp X.varpi))) =
      j α + j (WittVector.frobenius α) := by
  classical

  have hc0 : ∀ (a : Zp2 r) (i : Fin 2), MvPowerSeries.constantCoeff (X.act a i) = 0 := fun a => (X.isLawHom_act a).1
  have hϖ0 : ∀ i, MvPowerSeries.constantCoeff (X.varpi i) = 0 := X.isLawHom_varpi.1
  have hβϖ0 : ∀ i, MvPowerSeries.constantCoeff (((X.act β).comp X.varpi) i) = 0 := fun i =>
    MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hϖ0) hϖ0 (hc0 β i)

  have hlin : linearPart (Series.addVia X.F (X.act α) ((X.act β).comp X.varpi)) =
      linearPart (X.act α) + linearPart (X.act β) * linearPart X.varpi := by
    rw [← MvFormalGroup.linearPart_subst hϖ0 (X.act β)]
    exact MvFormalGroup.linearPart_subst_elim X.F (hc0 α) hβϖ0

  set M : Zp2 r → Matrix (Fin 2) (Fin 2) k := fun a => linearPart (X.act a) with hM
  set P : Matrix (Fin 2) (Fin 2) k := linearPart X.varpi with hP

  have hPM : ∀ a, P * M a = M (WittVector.frobenius a) * P := by
    intro a
    have h := congrArg linearPart (X.varpi_comp_act a)
    have e1 := MvFormalGroup.linearPart_subst (hc0 a) X.varpi
    have e2 := MvFormalGroup.linearPart_subst hϖ0 (X.act (WittVector.frobenius a))
    change linearPart (fun i => MvPowerSeries.subst (X.act a) (X.varpi i)) =
      linearPart (fun i => MvPowerSeries.subst X.varpi (X.act (WittVector.frobenius a) i)) at h
    rw [e1, e2] at h
    simpa only [hM, hP] using h

  set L₀ : Submodule k (Fin 2 → k) := X.lieZero j with hL₀
  set L₁ : Submodule k (Fin 2 → k) := X.lieOne j with hL₁
  obtain ⟨hcompl, hinv₀, hinv₁⟩ := hX
  have hact₀ : ∀ (a : Zp2 r) (v : Fin 2 → k), v ∈ L₀ → (M a).mulVecLin v = j a • v := by
    intro a v hv
    have := (Submodule.mem_iInf _).mp hv a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have hact₁ : ∀ (a : Zp2 r) (v : Fin 2 → k), v ∈ L₁ → (M a).mulVecLin v = j (WittVector.frobenius a) • v := by
    intro a v hv
    have := (Submodule.mem_iInf _).mp hv a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have hP₀ : ∀ v : Fin 2 → k, v ∈ L₀ → P.mulVecLin v ∈ L₁ := by
    intro v hv
    refine (Submodule.mem_iInf _).mpr fun b => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    change (M b).mulVecLin (P.mulVecLin v) = j (WittVector.frobenius b) • P.mulVecLin v
    rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, ← frobenius_frobenius b, ← hPM, frobenius_frobenius,
      Matrix.mulVecLin_mul, LinearMap.comp_apply, hact₀ _ v hv, map_smul]
  have hP₁ : ∀ v : Fin 2 → k, v ∈ L₁ → P.mulVecLin v ∈ L₀ := by
    intro v hv
    refine (Submodule.mem_iInf _).mpr fun b => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    change (M b).mulVecLin (P.mulVecLin v) = j b • P.mulVecLin v
    rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, ← frobenius_frobenius b, ← hPM, Matrix.mulVecLin_mul,
      LinearMap.comp_apply, hact₁ _ v hv, map_smul]

  let N : Fin 2 → Submodule k (Fin 2 → k) := ![L₀, L₁]
  have hN0 : N 0 = L₀ := rfl
  have hN1 : N 1 = L₁ := rfl
  have hN : DirectSum.IsInternal N := by
    refine (DirectSum.isInternal_submodule_iff_isCompl N (i := 0) (j := 1) (by decide) ?_).mpr ?_
    · ext i; fin_cases i <;> simp
    · rw [hN0, hN1]; exact hcompl
  haveI : ∀ i, Module.Free k ↥(N i) := fun i => Module.Free.of_divisionRing k _
  haveI : ∀ i, Module.Finite k ↥(N i) := fun i => Module.Finite.of_injective (N i).subtype (N i).injective_subtype

  have hrank₀ : Module.finrank k ↥L₀ = 1 := by haveI := hinv₀; exact Module.Invertible.finrank_eq_one k _
  have hrank₁ : Module.finrank k ↥L₁ = 1 := by haveI := hinv₁; exact Module.Invertible.finrank_eq_one k _
  have hmaps : ∀ i : Fin 2, Set.MapsTo ((M α).mulVecLin) ↑(N i) ↑(N i) := by
    intro i v hv
    fin_cases i
    · change v ∈ L₀ at hv; change (M α).mulVecLin v ∈ L₀; rw [hact₀ α v hv]; exact L₀.smul_mem _ hv
    · change v ∈ L₁ at hv; change (M α).mulVecLin v ∈ L₁; rw [hact₁ α v hv]; exact L₁.smul_mem _ hv
  have hT1 : (M α).trace = j α + j (WittVector.frobenius α) := by
    rw [← trace_mulVecLin, LinearMap.trace_eq_sum_trace_restrict hN hmaps, Fin.sum_univ_two]
    have e0 : ((M α).mulVecLin).restrict (hmaps 0) = j α • LinearMap.id := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      change (M α).mulVecLin v.1 = j α • v.1
      exact hact₀ α v.1 v.2
    have e1 : ((M α).mulVecLin).restrict (hmaps 1) = j (WittVector.frobenius α) • LinearMap.id := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      change (M α).mulVecLin v.1 = j (WittVector.frobenius α) • v.1
      exact hact₁ α v.1 v.2
    rw [e0, e1, map_smul, map_smul, LinearMap.trace_id, LinearMap.trace_id]
    change j α • ((Module.finrank k ↥L₀ : ℕ) : k) + j (WittVector.frobenius α) • ((Module.finrank k ↥L₁ : ℕ) : k) = _
    rw [hrank₀, hrank₁, Nat.cast_one, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

  have hT2 : (M β * P).trace = 0 := by
    rw [← trace_mulVecLin]
    refine LinearMap.trace_eq_zero_of_mapsTo_ne hN (fun i => i + 1) (by decide) fun i v hv => ?_
    fin_cases i
    · change v ∈ L₀ at hv
      change (M β * P).mulVecLin v ∈ L₁
      rw [Matrix.mulVecLin_mul, LinearMap.comp_apply, hact₁ β _ (hP₀ v hv)]
      exact L₁.smul_mem _ (hP₀ v hv)
    · change v ∈ L₁ at hv
      change (M β * P).mulVecLin v ∈ L₀
      rw [Matrix.mulVecLin_mul, LinearMap.comp_apply, hact₀ β _ (hP₁ v hv)]
      exact L₀.smul_mem _ (hP₁ v hv)
  rw [hlin, Matrix.trace_add, hT1, hT2, add_zero]

end alg

end Q4Asm

open Q4Asm in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] (j : Zp2 r →+* k)
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (act : ↥Λ → (A ⟶ A)) (hact : ∀ x : ↥Λ, act x ≫ f = f)
    (hact_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (act x) (hact x) (L.mul t P Q) = L.mul t (pushPt (act x) (hact x) P) (pushPt (act x) (hact x) Q))

    (X : FormalODModule r k) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates X.F θ)
    (hθact : ∀ (B' : Type) [CommRing B'] [Algebra k B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ (m : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval n
            (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) i) s) =
          pushPt (act m) (hact m) (θ B' s))

    (hX : X.IsSpecial j) :
    ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k')
      (V : Type) [AddCommGroup V] [Module k' V] [Module.Finite k' V] (τ : V → SchemeHomOver (tangentBase k' sk) f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k' sk) f, P ∈ Set.range τ ↔ IsTangentVector L k' sk P) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k' sk) (τ v) (τ w)) →
      (∀ (c : k') (v : V), (τ (c • v)).1 = tangentScale k' c ≫ (τ v).1) →
      ∀ (m : ↥Λ) (Φ : V →ₗ[k'] V), (∀ v : V, τ (Φ v) = pushPt (act m) (hact m) (τ v)) →
      ∀ n' : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n' : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k' V Φ = (n' : k') := by
  intro k' _ _ sk V _ _ _ τ hinj hrange hadd hsmul m Φ hΦ n' hn'
  have hc0 : ∀ (a' : Zp2 r) (i : Fin 2), MvPowerSeries.constantCoeff (X.act a' i) = 0 := fun a' => (X.isLawHom_act a').1
  have hϖ0 : ∀ i, MvPowerSeries.constantCoeff (X.varpi i) = 0 := X.isLawHom_varpi.1
  have hβϖ0 : ∀ i, MvPowerSeries.constantCoeff (((X.act (coord m).2).comp X.varpi) i) = 0 := fun i =>
    MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hϖ0) hϖ0 (hc0 _ i)
  have hφ0 : ∀ i, MvPowerSeries.constantCoeff
      (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) i) = 0 := by
    intro i
    refine MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_) (fun s => ?_) (X.F.constantCoeff_eq_zero i)
    all_goals rcases s with s | s
    exacts [hc0 _ s, hβϖ0 s, hc0 _ s, hβϖ0 s]
  have key := CerednikDrinfeld.QM.forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates L X.F θ hθ
    (act m) (hact m) (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi)) hφ0
    (by intro B' _ _ J n hJ s hs; exact hθact B' J n hJ m s hs) k' sk V τ hinj hrange hadd hsmul Φ hΦ
  rw [key, trace_linearPart_eq j X hX, ← map_add, hcoord.trace m n' hn', map_intCast, map_intCast]

end S_CerednikDrinfeld_QM_forall_trace_eq_intCast_of_isFormalCoordinates_of_isSpecial
end P2MW
export P2MW.S_CerednikDrinfeld_QM_forall_trace_eq_intCast_of_isFormalCoordinates_of_isSpecial (solution)
