-- Prove2me | solution 1 for CannonFloydParry.exists_mulEquiv_closure_range_piV1_SigmaPerm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T13:39:27.927485+00:00
-- url     : https://prove2.me/submissions/af288d15-10aa-49f9-a8de-ca804d18e6c9

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_V
import Theorems.Thm_CannonFloydParry_exists_mulEquiv_SigmaPres_SigmaPerm
import Theorems.Thm_CannonFloydParry_mk_sigmaGen_zero_eq_mk_sigmaGen_one
import Theorems.Thm_CannonFloydParry_piV1_relations
import Theorems.Thm_CannonFloydParry_exists_surjective_V1_V
import Mathlib

/-! `Π ≅ Σ` (CFP p. 247): `Π` is a quotient of `Σ` (Lemma 6.3), every proper quotient of `Σ`
identifies `s₀` and `s₁`, and `π₀ ≠ π₁` since their images in `V` differ. -/

namespace CannonFloydParry.PiSigma

open Equiv

/-! ### Evaluating the generators on `[0,1)` representatives -/

/-- The representative in `[0,1)` of a point of the circle. -/
noncomputable def ico (x : UnitAddCircle) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

lemma ico_nonneg (x : UnitAddCircle) : 0 ≤ ico x := (AddCircle.equivIco (1 : ℝ) 0 x).2.1

lemma ico_lt_one (x : UnitAddCircle) : ico x < 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 x).2.2
  unfold ico
  linarith

lemma ico_symm (y : Set.Ico (0 : ℝ) (0 + 1)) :
    ico ((AddCircle.equivIco (1 : ℝ) 0).symm y) = y := by
  simp [ico]

lemma ico_toCircle (f : UI ≃o UI) (x : UnitAddCircle) :
    ico (toCircle f x) = (f ⟨ico x, ico_nonneg x, (ico_lt_one x).le⟩ : ℝ) := by
  simp only [toCircle, Equiv.trans_apply, ico_symm]
  rfl

lemma ico_A (x : UnitAddCircle) : ico (symV FormalV.A x) = aFun (ico x) := by
  simp only [symV, ico_toCircle, mapA, restrict_coe, lineA_apply]

lemma ico_B (x : UnitAddCircle) : ico (symV FormalV.B x) = bFun (ico x) := by
  simp only [symV, ico_toCircle, mapB, restrict_coe, lineB_apply]

lemma ico_C (x : UnitAddCircle) : ico (symV FormalV.C x) = cFun (ico x) := by
  simp only [symV, mapC, Equiv.trans_apply, ico_symm]
  rfl

lemma ico_P (x : UnitAddCircle) : ico (symV FormalV.P x) = piFun (ico x) := by
  simp only [symV, mapPi0, Equiv.trans_apply, ico_symm]
  rfl

lemma aInv_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ aInv y ∧ aInv y ≤ 1 := by
  unfold aInv; split_ifs <;> constructor <;> linarith

lemma ico_Ainv (x : UnitAddCircle) : ico ((symV FormalV.A)⁻¹ x) = aInv (ico x) := by
  obtain ⟨h0, h1⟩ := aInv_mem (ico_nonneg x) (ico_lt_one x).le
  have hlt : aInv (ico x) < 0 + 1 := by
    rcases lt_or_eq_of_le h1 with h | h
    · simpa using h
    · exfalso
      have := aFun_aInv (ico x); rw [h] at this
      rw [aFun_of_mem3 (by norm_num) le_rfl] at this
      linarith [ico_lt_one x]
  let z := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨aInv (ico x), h0, hlt⟩
  have hz : symV FormalV.A z = x := by
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change ico (symV FormalV.A z) = ico x
    rw [ico_A, ico_symm]
    exact aFun_aInv (ico x)
  have : (symV FormalV.A)⁻¹ x = z := by rw [Perm.inv_eq_iff_eq]; exact hz.symm
  rw [this, ico_symm]

/-- `π₁ ≠ π₀` as maps of the circle. From `π₁ = B⁻¹C⁻¹A π₀ A⁻¹CB` we would get
`A π₀ A⁻¹ C B = C B π₀`; at `[0]` the left side gives `[3/4]` and the right side `[0]`. -/
lemma piV_one_ne : piV 1 ≠ symV FormalV.P := by
  intro h
  have hw : piV 1 = (symV FormalV.B)⁻¹ * (symV FormalV.C)⁻¹ * symV FormalV.A * symV FormalV.P *
      (symV FormalV.A)⁻¹ * symV FormalV.C * symV FormalV.B := by
    simp [piV, wordPi, wordC]; group
  have h' : symV FormalV.A * symV FormalV.P * (symV FormalV.A)⁻¹ * symV FormalV.C *
      symV FormalV.B = symV FormalV.C * symV FormalV.B * symV FormalV.P := by
    rw [h] at hw
    calc _ = symV FormalV.C * symV FormalV.B * ((symV FormalV.B)⁻¹ * (symV FormalV.C)⁻¹ *
          symV FormalV.A * symV FormalV.P * (symV FormalV.A)⁻¹ * symV FormalV.C *
          symV FormalV.B) := by group
      _ = _ := by rw [← hw]
  set x0 : UnitAddCircle := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨0, by norm_num, by norm_num⟩
  have hx0 : ico x0 = 0 := by rw [ico_symm]
  have e := congrArg (fun σ : Perm UnitAddCircle => ico (σ x0)) h'
  simp only [Perm.coe_mul, Function.comp_apply, ico_A, ico_B, ico_C, ico_P, ico_Ainv, hx0] at e
  rw [bFun_of_le_half (by norm_num), cFun, if_pos (by norm_num),
    aInv, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num),
    piFun, if_neg (by norm_num), if_neg (by norm_num), aFun_of_mem3 (by norm_num) (by norm_num),
    piFun, if_pos (by norm_num), bFun_of_le_half (by norm_num), cFun, if_neg (by norm_num),
    if_pos (by norm_num)] at e
  norm_num at e

/-! ### `Π` is a quotient of `Σ` -/

lemma rels_piV1 : ∀ r ∈ relsSigma, FreeGroup.lift piV1 r = 1 := by
  rintro r ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, j, hij, rfl⟩) <;>
    simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
  · exact (piV1_relations i).1
  · have h := (piV1_relations i).2.1
    calc (piV1 i * piV1 (i + 1)) ^ 3 = piV1 i * (piV1 (i + 1) * piV1 i) ^ 3 * (piV1 i)⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul]; group
      _ = 1 := by rw [h]; group
  · rw [sq]
    calc piV1 i * piV1 j * (piV1 i * piV1 j) = piV1 i * (piV1 j * piV1 i) * piV1 j := by group
      _ = (piV1 i * piV1 i) * (piV1 j * piV1 j) := by
          rw [← (piV1_relations i).2.2 j hij]; group
      _ = 1 := by rw [← sq, ← sq, (piV1_relations i).1, (piV1_relations j).1, one_mul]

/-- `sᵢ ↦ πᵢ`. -/
noncomputable def psi : SigmaPres →* V1 := PresentedGroup.toGroup rels_piV1

lemma psi_sg (i : ℕ) : psi (PresentedGroup.of i) = piV1 i := PresentedGroup.toGroup.of rels_piV1

lemma psi_range : psi.range = Subgroup.closure (Set.range piV1) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply]
  exact ⟨fun ⟨i, h⟩ => ⟨i, by rw [← h]; exact (psi_sg i).symm⟩,
    fun ⟨i, h⟩ => ⟨i, by rw [← h]; exact psi_sg i⟩⟩

end CannonFloydParry.PiSigma

open CannonFloydParry in
theorem solution :
    ∃ e : Subgroup.closure (Set.range piV1) ≃* SigmaPerm,
      ∀ i, e ⟨piV1 i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = sigmaGen i := by
  open PiSigma in
  obtain ⟨e, he⟩ := exists_mulEquiv_SigmaPres_SigmaPerm
  obtain ⟨φ, -, hφ⟩ := exists_surjective_V1_V
  have hψ : (V.subtype.comp φ).comp (PresentedGroup.mk relsV1) = FreeGroup.lift symV :=
    FreeGroup.ext_hom _ _ fun s => (hφ s).trans FreeGroup.lift_apply_of.symm
  have hψpi : ∀ n, V.subtype (φ (piV1 n)) = piV n := fun n =>
    DFunLike.congr_fun hψ (wordPi n)
  set θ : SigmaPerm →* V1 := psi.comp e.symm.toMonoidHom
  have hθ : ∀ i, θ (sigmaGen i) = piV1 i := by
    intro i
    show psi (e.symm (sigmaGen i)) = piV1 i
    rw [← he i, MulEquiv.symm_apply_apply]; exact psi_sg i
  have hinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hK
    have hq := mk_sigmaGen_zero_eq_mk_sigmaGen_one θ.ker hK
    rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, hθ, hθ, inv_mul_eq_one] at hq
    apply piV_one_ne
    rw [← hψpi, ← hq, hψpi]
    simp [piV, wordPi]
  have hrange : θ.range = Subgroup.closure (Set.range piV1) := by
    rw [← psi_range]
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨e.symm y, rfl⟩
    · rintro ⟨z, rfl⟩; exact ⟨e z, by simp [θ]⟩
  refine ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm, fun i => ?_⟩
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (hθ i).symm
