-- Prove2me | solution 1 for CuspForm.det_heckeULin_two_eq_pow_finrank_or_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d7619285-3ef7-52c9-b752-34333ce7acf7

import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_FreyPackage_ModMCarrier_levelInclusionLin_add_rescaleLin_eq_zero
import Theorems.Thm_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash
import Theorems.Thm_CuspForm_atkinLehnerLin_atkinLehnerLin
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_det_heckeULin_two_eq_pow_finrank_or_eq_neg
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"
set_option autoImplicit false

namespace CuspFormHeckeUDetAux

open scoped ModularForm

section LinAlg
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem det_eq_one_or_eq_neg_one_of_comp_self (e : V →ₗ[K] V) (he : e ∘ₗ e = LinearMap.id) :
    LinearMap.det e = 1 ∨ LinearMap.det e = -1 := by
  have h : LinearMap.det e * LinearMap.det e = 1 := by
    rw [← LinearMap.det_comp, he, LinearMap.det_id]
  exact mul_self_eq_one_iff.mp h

variable (K V) in
private def sigma : (V × V) →ₗ[K] (V × V) := (-(LinearMap.snd K V V)).prod (LinearMap.fst K V V)

@[scoped simp] private theorem sigma_apply (x y : V) : sigma K V (x, y) = (-y, x) := rfl

private theorem sigma_comp_sigma : sigma K V ∘ₗ sigma K V = -LinearMap.id := by
  apply LinearMap.ext; rintro ⟨x, y⟩; simp

private theorem det_sigma_mul_self [FiniteDimensional K V] :
    LinearMap.det (sigma K V) * LinearMap.det (sigma K V) = 1 := by
  rw [← LinearMap.det_comp, sigma_comp_sigma,
    show (-LinearMap.id : (V × V) →ₗ[K] (V × V)) = (-1 : K) • LinearMap.id from (neg_one_smul K _).symm,
    LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_prod, ← two_mul, pow_mul]
  norm_num

private def oldPlane (A : V →ₗ[K] V) (c : K) : (V × V) →ₗ[K] (V × V) :=
  (A ∘ₗ LinearMap.fst K V V + c • LinearMap.snd K V V).prod (-(LinearMap.fst K V V))

@[scoped simp] private theorem oldPlane_apply (A : V →ₗ[K] V) (c : K) (x y : V) :
    oldPlane A c (x, y) = (A x + c • y, -x) := rfl

private theorem det_oldPlane_comp_sigma [FiniteDimensional K V] (A : V →ₗ[K] V) (c : K) :
    LinearMap.det (oldPlane A c ∘ₗ sigma K V) = c ^ Module.finrank K V := by
  let W : Submodule K (V × V) := LinearMap.range (LinearMap.inl K V V)
  have hW : W ≤ W.comap (oldPlane A c ∘ₗ sigma K V) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨c • x, ?_⟩
    simp
  rw [LinearMap.det_eq_det_mul_det W (oldPlane A c ∘ₗ sigma K V) hW]
  have h1 : LinearMap.restrict (oldPlane A c ∘ₗ sigma K V) (p := W) (q := W) hW = c • LinearMap.id := by
    apply LinearMap.ext; rintro ⟨_, ⟨x, rfl⟩⟩
    ext <;> simp [LinearMap.restrict_apply, W]
  have h2 : W.mapQ W (oldPlane A c ∘ₗ sigma K V) hW = LinearMap.id := by
    apply LinearMap.ext; intro q
    induction q using Submodule.Quotient.induction_on with
    | H v =>
      obtain ⟨x, y⟩ := v
      rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq]
      refine ⟨c • x - A y - x, ?_⟩
      ext <;> simp [sub_eq_add_neg, add_comm, add_left_comm]
  rw [h1, h2, LinearMap.det_id, mul_one, LinearMap.det_smul, LinearMap.det_id, mul_one,
    LinearMap.finrank_range_of_inj LinearMap.inl_injective]

private theorem det_oldPlane [FiniteDimensional K V] (A : V →ₗ[K] V) (c : K) :
    LinearMap.det (oldPlane A c) = c ^ Module.finrank K V ∨
      LinearMap.det (oldPlane A c) = -c ^ Module.finrank K V := by
  have h := det_oldPlane_comp_sigma A c
  rw [LinearMap.det_comp] at h
  rcases mul_self_eq_one_iff.mp (det_sigma_mul_self (K := K) (V := V)) with h1 | h1
  · left; rwa [h1, mul_one] at h
  · right; rw [h1, mul_neg_one] at h; rw [← h, neg_neg]

end LinAlg

section Hecke
variable {R : ℕ} (p : ℕ)

private theorem natCast_mem_strictPeriods (j : ℕ) :
    (j : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 R)).strictPeriods := by
  simpa using AddSubgroup.nsmul_mem _ (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 R) j

private theorem heckeU_slash_heckeDiagMatrix (hp : p ≠ 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) :
    ModularForm.heckeU 2 p ((⇑f) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) = (p : ℂ) • ⇑f := by
  funext τ
  rw [ModularForm.heckeU_apply 2 hp, Pi.smul_apply, smul_eq_mul]
  have hper : ∀ j : ℕ, ((⇑f) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) (ModularForm.heckeMatrix p j • τ)
      = (p : ℂ) * f τ := by
    intro j
    rw [ModularForm.slash_heckeDiagMatrix_apply 2 hp]
    have hpt : ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p j • τ = ((j : ℝ) +ᵥ τ) := by
      apply UpperHalfPlane.ext
      rw [ModularForm.coe_heckeDiagMatrix_smul hp, ModularForm.coe_heckeMatrix_smul hp, UpperHalfPlane.coe_vadd]
      have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
      field_simp
      push_cast
      ring
    rw [hpt, SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f τ (natCast_mem_strictPeriods (R := R) j)]
    norm_num
  simp_rw [hper]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  field_simp

end Hecke

end CuspFormHeckeUDetAux
p2m_reactivate "P2MW.S_CuspForm_det_heckeULin_two_eq_pow_finrank_or_eq_neg.CuspFormHeckeUDetAux"

open CuspFormHeckeUDetAux in
theorem solution
    (p : ℕ) [Fact p.Prime] (R : ℕ) [NeZero R] (hpR : ¬ p ∣ R) :
    haveI : NeZero (R * p) := ⟨Nat.mul_ne_zero (NeZero.ne R) (Fact.out : p.Prime).ne_zero⟩
    LinearMap.det (CuspForm.heckeULin 2 (dvd_mul_left p R) :
        CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2)
        = (p : ℂ) ^ Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 R) 2) ∨
      LinearMap.det (CuspForm.heckeULin 2 (dvd_mul_left p R) :
        CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2)
        = -(p : ℂ) ^ Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 R) 2) := by
  haveI hRp : NeZero (R * p) := ⟨Nat.mul_ne_zero (NeZero.ne R) (Fact.out : p.Prime).ne_zero⟩
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2) :=
    CuspForm.finiteDimensional_Gamma0 (R * p) 2
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 R) 2) :=
    CuspForm.finiteDimensional_Gamma0 R 2

  let U : CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 :=
    CuspForm.heckeULin 2 (dvd_mul_left p R)
  show LinearMap.det U = _ ∨ LinearMap.det U = _
  let T : CuspForm (CongruenceSubgroup.Gamma0 R) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 R) 2 :=
    CuspForm.heckeTLin 2 hp hpR
  have hRM : R ∣ R * p := dvd_mul_right R p
  have hqRM : p * R ∣ R * p := by rw [mul_comm]
  let incl : CuspForm (CongruenceSubgroup.Gamma0 R) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 :=
    FreyPackage.ModMCarrier.levelInclusionLin hRM 2
  let resc : CuspForm (CongruenceSubgroup.Gamma0 R) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 :=
    FreyPackage.ModMCarrier.rescaleLin hqRM 2
  let C : (CuspForm (CongruenceSubgroup.Gamma0 R) 2 × CuspForm (CongruenceSubgroup.Gamma0 R) 2) →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 := incl.coprod resc

  have hUC : U ∘ₗ C = C ∘ₗ oldPlane T (p : ℂ) := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply DFunLike.ext'
    simp only [LinearMap.comp_apply, LinearMap.coprod_apply, oldPlane_apply, map_add, map_smul, map_neg,
      CuspForm.coe_add, CuspForm.coe_neg, U, T, C, incl, resc,
      CuspForm.coe_heckeULin_apply, CuspForm.coe_heckeTLin_apply,
      FreyPackage.ModMCarrier.coe_levelInclusionLin, FreyPackage.ModMCarrier.coe_rescaleLin_apply,
      ModularForm.heckeT_eq_heckeU_add, heckeU_slash_heckeDiagMatrix p hp0]
    abel

  have hCinj : Function.Injective C := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ h
    obtain ⟨hx, hy⟩ := FreyPackage.ModMCarrier.levelInclusionLin_add_rescaleLin_eq_zero hp hpR hRM hqRM x y
      (by simpa [C, incl, resc] using h)
    simp [hx, hy]

  let O : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2) := LinearMap.range C
  have hO : O ≤ O.comap U := by
    rintro _ ⟨v, rfl⟩
    refine ⟨oldPlane T (p : ℂ) v, ?_⟩
    change C (oldPlane T (p : ℂ) v) = U (C v)
    rw [← LinearMap.comp_apply, ← hUC, LinearMap.comp_apply]

  have hdetO : LinearMap.det (U.restrict hO) = LinearMap.det (oldPlane T (p : ℂ)) := by
    let e := LinearEquiv.ofInjective C hCinj
    have he : U.restrict hO = (e : _ →ₗ[ℂ] O) ∘ₗ oldPlane T (p : ℂ) ∘ₗ (e.symm : O →ₗ[ℂ] _) := by
      apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := e.surjective w
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        LinearMap.coe_restrict_apply, e, LinearEquiv.ofInjective_apply]
      rw [← LinearMap.comp_apply, hUC, LinearMap.comp_apply]
    rw [he, LinearMap.det_conj]

  let Wd : ModularForm.AtkinLehnerDatum (R * p) p := FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd R p hp hpR
  let Wl : CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 :=
    CuspForm.atkinLehnerLin Wd 2
  have htr : ∀ v, U (Wl v) + v ∈ O := by
    intro v
    obtain ⟨G, hG⟩ := CuspForm.exists_coe_eq_add_smul_heckeU_alSlash p hp Wd 2 v
    refine ⟨((G : CuspForm (CongruenceSubgroup.Gamma0 R) 2), 0), ?_⟩
    apply DFunLike.ext'
    simp only [C, incl, resc, U, Wl, LinearMap.coprod_apply, map_zero, add_zero, CuspForm.coe_add,
      FreyPackage.ModMCarrier.coe_levelInclusionLin, CuspForm.coe_heckeULin_apply, CuspForm.coe_atkinLehnerLin_apply]
    refine hG.trans ?_
    norm_num [add_comm]
  have key : ∀ v, U (U v) - v ∈ O := by
    intro v
    have hA : U v + Wl v ∈ O := by
      simpa [Wl, CuspForm.atkinLehnerLin_atkinLehnerLin] using htr (Wl v)
    have hB : U (U v + Wl v) ∈ O := hO hA
    have hrw : U (U v) - v = U (U v + Wl v) - (U (Wl v) + v) := by rw [map_add]; abel
    rw [hrw]
    exact O.sub_mem hB (htr v)
  have hq : (O.mapQ O U hO) ∘ₗ (O.mapQ O U hO) = LinearMap.id := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H v =>
      rw [LinearMap.comp_apply, Submodule.mapQ_apply, Submodule.mapQ_apply, LinearMap.id_apply,
        Submodule.Quotient.eq]
      exact key v

  rw [LinearMap.det_eq_det_mul_det O U hO, hdetO]
  rcases det_oldPlane T (p : ℂ) with h1 | h1 <;>
    rcases det_eq_one_or_eq_neg_one_of_comp_self _ hq with h2 | h2 <;> simp [h1, h2]

end S_CuspForm_det_heckeULin_two_eq_pow_finrank_or_eq_neg
end P2MW
export P2MW.S_CuspForm_det_heckeULin_two_eq_pow_finrank_or_eq_neg (solution)
