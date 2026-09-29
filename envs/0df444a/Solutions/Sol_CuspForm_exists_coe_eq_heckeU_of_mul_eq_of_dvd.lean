-- Prove2me | solution 1 for CuspForm.exists_coe_eq_heckeU_of_mul_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/01ec0107-2b7f-5eba-aadc-2b9fd3a287cf

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_coe_eq_heckeU_of_mul_eq_of_dvd

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm OnePoint Function
open scoped MatrixGroups ModularForm

namespace AlliAux1L7

theorem sum_slash {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ) :
    (∑ i ∈ s, f i) ∣[k] g = ∑ i ∈ s, (f i ∣[k] g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

def hM (q j : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, (j : ℤ); 0, (q : ℤ)]

theorem hM_map_eq {q : ℕ} (hq : q ≠ 0) (j : ℕ) :
    (hM q j).map (algebraMap ℤ ℝ) = ((heckeMatrix q j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [val_heckeMatrix hq]; unfold hM
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem map_int_mul_eq (A C : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * C).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * C.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

theorem mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

section perm

variable {q : ℕ} [NeZero q]

def σ (b d : ℤ) (j : ℕ) : ℕ := (((b * d + (j : ℤ) * d * d : ℤ)) : ZMod q).val

def σinv (a b d : ℤ) (j : ℕ) : ℕ :=
  ((((j : ℕ) : ZMod q) - ((b * d : ℤ) : ZMod q)) * ((a : ℤ) : ZMod q) ^ 2).val

theorem σ_lt (b d : ℤ) (j : ℕ) : σ (q := q) b d j < q := ZMod.val_lt _

theorem σinv_lt (a b d : ℤ) (j : ℕ) : σinv (q := q) a b d j < q := ZMod.val_lt _

theorem σ_cast (b d : ℤ) (j : ℕ) :
    ((σ (q := q) b d j : ℕ) : ZMod q)
      = ((b : ℤ) : ZMod q) * ((d : ℤ) : ZMod q)
        + ((j : ℕ) : ZMod q) * ((d : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) := by
  unfold σ
  rw [ZMod.natCast_zmod_val]
  push_cast
  ring

theorem σinv_cast (a b d : ℤ) (j : ℕ) :
    ((σinv (q := q) a b d j : ℕ) : ZMod q)
      = (((j : ℕ) : ZMod q) - ((b : ℤ) : ZMod q) * ((d : ℤ) : ZMod q)) * ((a : ℤ) : ZMod q) ^ 2 := by
  unfold σinv
  rw [ZMod.natCast_zmod_val]
  push_cast
  ring

theorem σinv_σ {a b d : ℤ} (had : ((a : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) = 1) {j : ℕ}
    (hj : j < q) : σinv (q := q) a b d (σ (q := q) b d j) = j := by
  unfold σinv
  have h : (((σ (q := q) b d j : ℕ) : ZMod q) - ((b * d : ℤ) : ZMod q)) * ((a : ℤ) : ZMod q) ^ 2
      = ((j : ℕ) : ZMod q) := by
    rw [σ_cast]
    push_cast
    linear_combination (((j : ℕ) : ZMod q) * (((a : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) + 1)) * had
  rw [h, ZMod.val_cast_of_lt hj]

theorem σ_σinv {a b d : ℤ} (had : ((a : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) = 1) {j : ℕ}
    (hj : j < q) : σ (q := q) b d (σinv (q := q) a b d j) = j := by
  unfold σ
  have h : ((b * d + ((σinv (q := q) a b d j : ℕ) : ℤ) * d * d : ℤ) : ZMod q)
      = ((j : ℕ) : ZMod q) := by
    push_cast
    rw [σinv_cast]
    linear_combination ((((j : ℕ) : ZMod q) - ((b : ℤ) : ZMod q) * ((d : ℤ) : ZMod q)) *
      (((a : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) + 1)) * had
  rw [h, ZMod.val_cast_of_lt hj]

end perm

theorem ad_eq_one {q : ℕ} {γ : SL(2, ℤ)} (hc : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod q)
      = 1 := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hc0 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have h := congrArg (fun z : ℤ => (z : ZMod q)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc0, mul_zero, sub_zero] at h
  exact h

theorem exists_conj {q R : ℕ} [NeZero q] (hqR : q ∣ R) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 R) (j : ℕ) :
    ∃ γ' : SL(2, ℤ), γ' ∈ CongruenceSubgroup.Gamma0 (q * R) ∧
      hM q j * (γ : Matrix (Fin 2) (Fin 2) ℤ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ) *
          hM q (σ (q := q) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) j) := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hRc : (R : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h := hγ; rw [CongruenceSubgroup.Gamma0_mem] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have hqc : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (Int.natCast_dvd_natCast.mpr hqR).trans hRc
  have had := ad_eq_one hqc
  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  set j' : ℕ := σ (q := q) b d j with hj'
  have hγmat : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _

  have hdiv : (q : ℤ) ∣ b + (j : ℤ) * d - (a + (j : ℤ) * c) * (j' : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hc0 : ((c : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hqc
    have hjc : ((j' : ℕ) : ZMod q) = ((b : ℤ) : ZMod q) * ((d : ℤ) : ZMod q)
        + ((j : ℕ) : ZMod q) * ((d : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) := by
      rw [hj', σ_cast]
    push_cast
    rw [hc0, hjc]
    linear_combination (-(((b : ℤ) : ZMod q) + ((j : ℕ) : ZMod q) * ((d : ℤ) : ZMod q))) * had
  obtain ⟨b', hb'⟩ := hdiv
  obtain ⟨c₁, hc₁⟩ := hRc
  have hdetγ' : Matrix.det !![a + (j : ℤ) * c, b'; (q : ℤ) * c, d - c * (j' : ℤ)] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + c * hb'
  refine ⟨⟨_, hdetγ'⟩, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    show (((q : ℤ) * c : ℤ) : ZMod (q * R)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc₁]
    exact ⟨c₁, by push_cast; ring⟩
  · show hM q j * (γ : Matrix (Fin 2) (Fin 2) ℤ)
      = !![a + (j : ℤ) * c, b'; (q : ℤ) * c, d - c * (j' : ℤ)] * hM q j'
    rw [hγmat]; unfold hM
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i k => ?_
    fin_cases i <;> fin_cases k
    · show (1 * a + (j : ℤ) * c : ℤ) = (a + (j : ℤ) * c) * 1 + b' * 0; ring
    · show (1 * b + (j : ℤ) * d : ℤ) = (a + (j : ℤ) * c) * (j' : ℤ) + b' * (q : ℤ)
      linear_combination hb'
    · show (0 * a + (q : ℤ) * c : ℤ) = (q : ℤ) * c * 1 + (d - c * (j' : ℤ)) * 0; ring
    · show (0 * b + (q : ℤ) * d : ℤ) = (q : ℤ) * c * (j' : ℤ) + (d - c * (j' : ℤ)) * (q : ℤ); ring

theorem exists_conj_GL {q R : ℕ} [NeZero q] (hqR : q ∣ R) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 R) (j : ℕ) :
    ∃ γ' : SL(2, ℤ), γ' ∈ CongruenceSubgroup.Gamma0 (q * R) ∧
      heckeMatrix q j * (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
        = (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) *
          heckeMatrix q (σ (q := q) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) j) := by
  obtain ⟨γ', hγ', hconj⟩ := exists_conj hqR hγ j
  refine ⟨γ', hγ', ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, mapGL_coe_eq, mapGL_coe_eq, ← hM_map_eq (NeZero.ne q),
    ← hM_map_eq (NeZero.ne q), ← map_int_mul_eq, ← map_int_mul_eq, hconj]

theorem heckeU_slash_eq {m q R : ℕ} [NeZero m] [NeZero q] (hqR : q * R = m) (hq : q ∣ R)
    (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 R) :
    heckeU 2 q ⇑F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = heckeU 2 q ⇑F := by
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set d : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  have hRc : (R : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h := hγ; rw [CongruenceSubgroup.Gamma0_mem] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have had : ((a : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) = 1 :=
    ad_eq_one ((Int.natCast_dvd_natCast.mpr hq).trans hRc)
  rw [heckeU_def, sum_slash]

  have hterm : ∀ j ∈ Finset.range q,
      (⇑F ∣[(2 : ℤ)] heckeMatrix q j) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
        = ⇑F ∣[(2 : ℤ)] heckeMatrix q (σ (q := q) b d j) := by
    intro j _
    obtain ⟨γ', hγ', hconj⟩ := exists_conj_GL hq hγ j
    rw [← SlashAction.slash_mul, hconj, SlashAction.slash_mul]
    congr 1
    rw [hqR] at hγ'
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map.mpr ⟨γ', hγ', rfl⟩)
  rw [Finset.sum_congr rfl hterm]

  refine Finset.sum_nbij' (σ (q := q) b d) (σinv (q := q) a b d) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_range.mpr (σ_lt b d j)
  · intro j _; exact Finset.mem_range.mpr (σinv_lt a b d j)
  · intro j hj; exact σinv_σ had (Finset.mem_range.mp hj)
  · intro j hj; exact σ_σinv had (Finset.mem_range.mp hj)
  · intro j _; rfl

def ubundle {m q R : ℕ} [NeZero m] [NeZero q] [NeZero R] (hqR : q * R = m) (hq : q ∣ R)
    (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2) : CuspForm (CongruenceSubgroup.Gamma0 R) 2 where
  toFun := heckeU 2 q ⇑F
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    exact heckeU_slash_eq hqR hq F hg
  holo' := mdifferentiable_heckeU (CuspFormClass.holo F) 2 q
  zero_at_cusps' {c} hc := by
    refine CuspFormClass.isZeroAt_heckeU F q ?_
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact hc

end AlliAux1L7

theorem solution
    {m q R : ℕ} [NeZero m] (hqR : q * R = m) (hq : q ∣ R)
    (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 R) 2, ⇑g = ModularForm.heckeU 2 q ⇑F := by
  haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne m (by rw [← hqR, zero_mul])⟩
  haveI : NeZero R := ⟨by rintro rfl; exact NeZero.ne m (by rw [← hqR, mul_zero])⟩
  exact ⟨AlliAux1L7.ubundle hqR hq F, rfl⟩

end
end S_CuspForm_exists_coe_eq_heckeU_of_mul_eq_of_dvd
end P2MW
export P2MW.S_CuspForm_exists_coe_eq_heckeU_of_mul_eq_of_dvd (solution)
