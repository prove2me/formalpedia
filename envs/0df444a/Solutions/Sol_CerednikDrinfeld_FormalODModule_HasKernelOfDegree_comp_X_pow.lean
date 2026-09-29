-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ed3980fe-1eea-59cc-aa52-e6bf581e25db

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_X_pow

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace R4KerFrob

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff subst_X coe_substAlgHom)
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

universe u

variable {B : Type u} [CommRing B]

local notation "S" => MvPowerSeries (Fin 2) B
local notation "Deg" => (Fin 2 →₀ ℕ)

def xq (B : Type u) [CommRing B] (q : ℕ) : Series B :=
  fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q

theorem xq_def (q : ℕ) : xq B q = fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q := rfl

theorem constantCoeff_xq {q : ℕ} (hq : q ≠ 0) (i : Fin 2) : constantCoeff (xq B q i) = 0 := by
  rw [xq, map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]

theorem hasSubst_xq {q : ℕ} (hq : q ≠ 0) : HasSubst (xq B q) := hasSubst_of_constantCoeff_zero (constantCoeff_xq hq)

theorem prod_xq_pow {q : ℕ} (hq : q ≠ 0) (d : Deg) : (d.prod fun s n => xq B q s ^ n) = MvPowerSeries.monomial (q • d) (1 : B) := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have h : ∀ i : Fin 2, xq B q i ^ d i = MvPowerSeries.monomial (Finsupp.single i ((q • d) i)) (1 : B) := by
    intro i
    rw [xq, ← pow_mul, MvPowerSeries.X_pow_eq, Finsupp.smul_apply, smul_eq_mul]
  simp_rw [h]
  rw [MvPowerSeries.prod_monomial, Finset.prod_const_one, Finsupp.univ_sum_single]

theorem smul_deg_injective {q : ℕ} (hq : q ≠ 0) {d d' : Deg} (h : q • d = q • d') : d = d' := by
  ext i
  have := DFunLike.congr_fun h i
  simp only [Finsupp.smul_apply, smul_eq_mul] at this
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) this

theorem le_smul_self {q : ℕ} (hq : q ≠ 0) (d : Deg) : d ≤ q • d := by
  intro i
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hq)

def theta {q : ℕ} (h : S) : S := subst (xq B q) h

theorem theta_def {q : ℕ} (h : S) : theta (q := q) h = subst (xq B q) h := rfl

theorem coeff_theta {q : ℕ} (hq : q ≠ 0) (h : S) (n : Deg) :
    coeff n (theta (q := q) h) = ∑ d ∈ Finset.Iic n, if n = q • d then coeff d h else 0 := by
  classical
  rw [theta, MvPowerSeries.coeff_subst (hasSubst_xq hq)]
  have hh : ∀ d : Deg,
      coeff d h • coeff n (d.prod fun s m => xq B q s ^ m) = if n = q • d then coeff d h else 0 := by
    intro d
    rw [prod_xq_pow hq, MvPowerSeries.coeff_monomial]
    by_cases hd : n = q • d
    · rw [if_pos hd, if_pos hd, smul_eq_mul, mul_one]
    · rw [if_neg hd, if_neg hd, smul_zero]
  simp_rw [hh]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  rw [Function.mem_support] at hd
  have hnd : n = q • d := by by_contra h'; exact hd (if_neg h')
  rw [Finset.mem_coe, Finset.mem_Iic, hnd]
  exact le_smul_self hq d

theorem theta_monomial {q : ℕ} (hq : q ≠ 0) (d : Deg) (c : B) :
    theta (q := q) (MvPowerSeries.monomial d c) = MvPowerSeries.monomial (q • d) c := by
  classical
  ext n
  rw [coeff_theta hq, MvPowerSeries.coeff_monomial]
  simp_rw [MvPowerSeries.coeff_monomial]
  by_cases hn : n = q • d
  · rw [if_pos hn, Finset.sum_eq_single d]
    · rw [if_pos hn, if_pos rfl]
    · intro d' _ hd'
      by_cases h1 : n = q • d'
      · exact absurd (smul_deg_injective hq (hn.symm.trans h1)).symm hd'
      · rw [if_neg h1]
    · intro hd
      exfalso; apply hd
      rw [Finset.mem_Iic, hn]; exact le_smul_self hq d
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro d' _
    by_cases h1 : n = q • d'
    · rw [if_pos h1, if_neg]
      rintro rfl; exact hn h1
    · rw [if_neg h1]

theorem theta_add {q : ℕ} (hq : q ≠ 0) (h h' : S) : theta (q := q) (h + h') = theta (q := q) h + theta (q := q) h' := by
  rw [theta, theta, theta, ← coe_substAlgHom (hasSubst_xq hq), map_add]

theorem theta_mul {q : ℕ} (hq : q ≠ 0) (h h' : S) : theta (q := q) (h * h') = theta (q := q) h * theta (q := q) h' := by
  rw [theta, theta, theta, ← coe_substAlgHom (hasSubst_xq hq), map_mul]

theorem theta_sum {q : ℕ} (hq : q ≠ 0) {ι : Type*} (s : Finset ι) (h : ι → S) :
    theta (q := q) (∑ i ∈ s, h i) = ∑ i ∈ s, theta (q := q) (h i) := by
  simp only [theta_def]
  rw [← coe_substAlgHom (hasSubst_xq hq), map_sum]

theorem comp_xq {q : ℕ} (φ : Series B) : φ.comp (xq B q) = fun i => theta (q := q) (φ i) := rfl

abbrev Idx (q : ℕ) : Type := Fin 2 → Fin q

def emb {q : ℕ} (α : Idx q) (m : Deg) : Deg :=
  Finsupp.equivFunOnFinite.symm fun i => (α i : ℕ) + q * m i

@[scoped simp] theorem emb_apply {q : ℕ} (α : Idx q) (m : Deg) (i : Fin 2) : emb α m i = (α i : ℕ) + q * m i := rfl

def resIdx {q : ℕ} (hq : q ≠ 0) (n : Deg) : Idx q := fun i => ⟨n i % q, Nat.mod_lt _ (Nat.pos_of_ne_zero hq)⟩

def quo (q : ℕ) (n : Deg) : Deg := Finsupp.equivFunOnFinite.symm fun i => n i / q

@[scoped simp] theorem quo_apply (q : ℕ) (n : Deg) (i : Fin 2) : quo q n i = n i / q := rfl

@[scoped simp] theorem resIdx_apply {q : ℕ} (hq : q ≠ 0) (n : Deg) (i : Fin 2) : ((resIdx hq n i : Fin q) : ℕ) = n i % q := rfl

theorem emb_resIdx_quo {q : ℕ} (hq : q ≠ 0) (n : Deg) : emb (resIdx hq n) (quo q n) = n := by
  ext i; simp only [emb_apply, resIdx_apply, quo_apply]; exact Nat.mod_add_div (n i) q

theorem resIdx_emb {q : ℕ} (hq : q ≠ 0) (α : Idx q) (m : Deg) : resIdx hq (emb α m) = α := by
  funext i; apply Fin.ext
  simp only [resIdx_apply, emb_apply]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (α i).isLt]

theorem quo_emb {q : ℕ} (hq : q ≠ 0) (α : Idx q) (m : Deg) : quo q (emb α m) = m := by
  ext i
  simp only [quo_apply, emb_apply]
  rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hq), Nat.div_eq_of_lt (α i).isLt, zero_add]

theorem emb_injective {q : ℕ} (hq : q ≠ 0) {α α' : Idx q} {m m' : Deg} (h : emb α m = emb α' m') : α = α' ∧ m = m' := by
  constructor
  · rw [← resIdx_emb hq α m, h, resIdx_emb hq]
  · rw [← quo_emb hq α m, h, quo_emb hq]

def decim {q : ℕ} (hq : q ≠ 0) : S ≃ₗ[B] (Idx q → S) where
  toFun f α := fun m => f (emb α m)
  invFun g := fun n => g (resIdx hq n) (quo q n)
  map_add' f f' := by funext α; rfl
  map_smul' c f := by funext α; rfl
  left_inv f := by
    funext n
    show f (emb (resIdx hq n) (quo q n)) = f n
    rw [emb_resIdx_quo]
  right_inv g := by
    funext α m
    show g (resIdx hq (emb α m)) (quo q (emb α m)) = g α m
    rw [resIdx_emb, quo_emb hq]

theorem coeff_decim {q : ℕ} (hq : q ≠ 0) (f : S) (α : Idx q) (m : Deg) : coeff m (decim hq f α) = coeff (emb α m) f := rfl

theorem smul_le_emb_iff {q : ℕ} (hq : q ≠ 0) (α : Idx q) (d m : Deg) : q • d ≤ emb α m ↔ d ≤ m := by
  constructor
  · intro h i
    have hi := h i
    simp only [Finsupp.smul_apply, smul_eq_mul, emb_apply] at hi
    by_contra hlt
    push Not at hlt
    have : q * (m i + 1) ≤ q * d i := Nat.mul_le_mul_left _ hlt
    have hα := (α i).isLt
    nlinarith
  · intro h i
    simp only [Finsupp.smul_apply, smul_eq_mul, emb_apply]
    exact (Nat.mul_le_mul_left q (h i)).trans (Nat.le_add_left _ _)

theorem emb_sub_smul {q : ℕ} (hq : q ≠ 0) (α : Idx q) {d m : Deg} (h : d ≤ m) : emb α m - q • d = emb α (m - d) := by
  ext i
  simp only [Finsupp.coe_tsub, Pi.sub_apply, emb_apply, Finsupp.smul_apply, smul_eq_mul]
  have hle : q * d i ≤ q * m i := Nat.mul_le_mul_left q (h i)
  rw [Nat.mul_sub]
  omega

theorem decim_theta_monomial_mul {q : ℕ} (hq : q ≠ 0) (d : Deg) (c : B) (f : S) (α : Idx q) :
    decim hq (theta (q := q) (MvPowerSeries.monomial d c) * f) α = MvPowerSeries.monomial d c * decim hq f α := by
  ext m
  rw [coeff_decim, theta_monomial hq, MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul]
  by_cases hdm : d ≤ m
  · rw [if_pos ((smul_le_emb_iff hq α d m).2 hdm), if_pos hdm, emb_sub_smul hq α hdm, coeff_decim]
  · rw [if_neg (fun h => hdm ((smul_le_emb_iff hq α d m).1 h)), if_neg hdm]

theorem coeff_decim_theta_mul_eq_zero {q : ℕ} (hq : q ≠ 0) (h f : S) (α : Idx q) (m : Deg) (hh : ∀ d, d ≤ m → coeff d h = 0) :
    coeff m (decim hq (theta (q := q) h * f) α) = 0 ∧ coeff m (h * decim hq f α) = 0 := by
  classical
  constructor
  · rw [coeff_decim, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx1 : x.1 ≤ emb α m := by rw [← hx]; exact le_self_add
    rw [coeff_theta hq]
    rw [Finset.sum_eq_zero, zero_mul]
    intro d hd
    by_cases h1 : x.1 = q • d
    · rw [if_pos h1]
      apply hh
      rw [← smul_le_emb_iff hq α, ← h1]; exact hx1
    · rw [if_neg h1]
  · rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hh x.1 (by rw [← hx]; exact le_self_add), zero_mul]

theorem decim_theta_mul {q : ℕ} (hq : q ≠ 0) (h f : S) (α : Idx q) :
    decim hq (theta (q := q) h * f) α = h * decim hq f α := by
  classical
  ext m

  set P : S := ∑ d ∈ Finset.Iic m, MvPowerSeries.monomial d (coeff d h) with hP
  set g : S := h - P with hg
  have hgcoeff : ∀ a, a ≤ m → coeff a g = 0 := by
    intro a ha
    rw [hg, map_sub, hP, map_sum]
    simp_rw [MvPowerSeries.coeff_monomial]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_Iic.2 ha), sub_self]
  have hf : h = P + g := by rw [hg]; abel
  obtain ⟨hz1, hz2⟩ := coeff_decim_theta_mul_eq_zero hq g f α m hgcoeff
  have hPeq : decim hq (theta (q := q) P * f) α = P * decim hq f α := by
    rw [hP, theta_sum hq, Finset.sum_mul, map_sum, Finset.sum_mul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact decim_theta_monomial_mul hq d _ f α
  conv_lhs => rw [hf, theta_add hq, add_mul, map_add, Pi.add_apply, map_add, hPeq, hz1, add_zero]
  conv_rhs => rw [hf, add_mul, map_add, hz2, add_zero]

abbrev I (φ : Series B) : Submodule B S := (Ideal.span (Set.range φ)).restrictScalars B

abbrev J (q : ℕ) (φ : Series B) : Submodule B S := (Ideal.span (Set.range (φ.comp (xq B q)))).restrictScalars B

theorem decim_mem_pi_of_mem {q : ℕ} (hq : q ≠ 0) (φ : Series B) (f : S)
    (hf : f ∈ Ideal.span (Set.range (φ.comp (xq B q)))) :
    decim hq f ∈ Submodule.pi Set.univ (fun _ : Idx q => I φ) := by
  rw [Ideal.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, rfl⟩ := hf
  rw [Submodule.mem_pi]
  intro α _
  rw [map_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  show decim hq (c i * theta (q := q) (φ i)) α ∈ Ideal.span (Set.range φ)
  rw [mul_comm, decim_theta_mul hq]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem symm_mem_of_mem_pi {q : ℕ} (hq : q ≠ 0) (φ : Series B) (g : Idx q → S)
    (hg : g ∈ Submodule.pi Set.univ (fun _ : Idx q => I φ)) :
    (decim hq).symm g ∈ Ideal.span (Set.range (φ.comp (xq B q))) := by
  classical

  have hdec : g = ∑ α : Idx q, Pi.single α (g α) := by
    rw [Finset.univ_sum_single]
  rw [hdec, map_sum]
  refine Ideal.sum_mem _ fun α _ => ?_
  have hα : g α ∈ Ideal.span (Set.range φ) := (Submodule.mem_pi.1 hg) α (Set.mem_univ _)
  rw [Ideal.mem_span_range_iff_exists_fun] at hα
  obtain ⟨c, hc⟩ := hα
  rw [← hc]
  have hsingle : (Pi.single α (∑ i, c i * φ i) : Idx q → S) = ∑ i, Pi.single α (c i * φ i) :=
    map_sum (AddMonoidHom.single (fun _ : Idx q => S) α) _ _
  rw [hsingle, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_

  have key : (decim hq).symm (Pi.single α (c i * φ i)) =
      theta (q := q) (φ i) * (decim hq).symm (Pi.single α (c i)) := by
    apply (decim hq).injective
    rw [LinearEquiv.apply_symm_apply]
    funext β
    rw [decim_theta_mul hq, LinearEquiv.apply_symm_apply]
    by_cases hβ : β = α
    · subst hβ; simp [mul_comm]
    · simp [Pi.single_eq_of_ne hβ]
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem map_decim_J {q : ℕ} (hq : q ≠ 0) (φ : Series B) :
    Submodule.map ((decim hq : S ≃ₗ[B] (Idx q → S)) : S →ₗ[B] (Idx q → S)) (J q φ) =
    Submodule.pi Set.univ (fun _ : Idx q => I φ) := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact decim_mem_pi_of_mem hq φ f hf
  · intro g hg
    refine ⟨(decim hq).symm g, symm_mem_of_mem_pi hq φ g hg, ?_⟩
    simp

def kerEquiv {q : ℕ} (hq : q ≠ 0) (φ : Series B) :
    FormalODModule.KerAlgebra (φ.comp (xq B q)) ≃ₗ[B] (Idx q → FormalODModule.KerAlgebra φ) := by
  classical
  refine (Submodule.Quotient.restrictScalarsEquiv B (Ideal.span (Set.range (φ.comp (xq B q))))).symm ≪≫ₗ ?_
  refine Submodule.Quotient.equiv (J q φ) (Submodule.pi Set.univ (fun _ : Idx q => I φ)) (decim hq) (map_decim_J hq φ) ≪≫ₗ ?_
  refine Submodule.quotientPi (fun _ : Idx q => I φ) ≪≫ₗ ?_
  exact LinearEquiv.piCongrRight fun _ => Submodule.Quotient.restrictScalarsEquiv B (Ideal.span (Set.range φ))

theorem map_comp_xq {q : ℕ} (φ : Series B) {B' : Type u} [CommRing B'] (f : B →+* B') (hq : q ≠ 0) :
    (φ.comp (xq B q)).map f = (φ.map f).comp (xq B' q) := by
  rw [Series.map_comp f _ _ (constantCoeff_xq hq)]
  congr 1
  funext i
  show MvPowerSeries.map f ((MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q) = _
  rw [map_pow, MvPowerSeries.map_X]; rfl

theorem main {q : ℕ} (hq : q ≠ 0) (φ : Series B) {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) :
    FormalODModule.HasKernelOfDegree (φ.comp (xq B q)) (d * q ^ 2) := by
  classical
  obtain ⟨hfin, hproj, hfib⟩ := hφ
  refine ⟨?_, ?_, fun κ _ f => ?_⟩
  · haveI : Module.Finite B (Idx q → FormalODModule.KerAlgebra φ) := Module.Finite.pi
    exact Module.Finite.equiv (kerEquiv hq φ).symm
  · haveI : Module.Projective B (Idx q → FormalODModule.KerAlgebra φ) :=
      Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (M := fun _ : Idx q => FormalODModule.KerAlgebra φ))
    exact Module.Projective.of_equiv (kerEquiv hq φ).symm
  · rw [map_comp_xq φ f hq, (kerEquiv hq (φ.map f)).finrank_eq]
    have hcard : Fintype.card (Idx q) = q ^ 2 := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    by_cases hK : Module.Finite κ (FormalODModule.KerAlgebra (φ.map f))
    · rw [Module.finrank_pi_fintype, hfib κ f, Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard, mul_comm]
    ·
      have hd : d = 0 := by rw [← hfib κ f, Module.finrank_of_not_finite hK]
      have hK' : ¬ Module.Finite κ (Idx q → FormalODModule.KerAlgebra (φ.map f)) := by
        intro hfin'
        apply hK
        let α₀ : Idx q := fun _ => ⟨0, Nat.pos_of_ne_zero hq⟩
        exact Module.Finite.of_surjective (LinearMap.proj (R := κ) (φ := fun _ : Idx q => FormalODModule.KerAlgebra (φ.map f)) α₀)
          (fun x => ⟨fun _ => x, rfl⟩)
      rw [Module.finrank_of_not_finite hK', hd, zero_mul]

end R4KerFrob
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_X_pow.R4KerFrob"

universe u in
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem solution
    {B : Type u} [CommRing B] {φ : Series B} {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d)
    {q : ℕ} (hq : q ≠ 0) :
    FormalODModule.HasKernelOfDegree (φ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q)
      (d * q ^ 2) :=
  R4KerFrob.main hq φ hφ

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_X_pow.R4KerFrob"

end S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_X_pow
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_X_pow (solution)
