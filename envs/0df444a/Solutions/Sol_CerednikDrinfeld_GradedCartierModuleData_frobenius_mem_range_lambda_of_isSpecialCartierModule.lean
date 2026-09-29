-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.frobenius_mem_range_lambda_of_isSpecialCartierModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/cc3aa150-f883-5998-aa26-454d30e4b806

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_frobenius_mem_range_lambda_of_isSpecialCartierModule

set_option autoImplicit false

namespace FSubPiVAux

open WittVector

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

noncomputable def zInt : 𝕎 ℤ := (p : 𝕎 ℤ) - teichmuller p (p : ℤ)

theorem zInt_coeff_zero : (zInt p).coeff 0 = 0 := by
  have h : constantCoeff (zInt p) = constantCoeff (p : 𝕎 ℤ) - constantCoeff (teichmuller p (p : ℤ)) := by
    rw [zInt, map_sub]
  rw [constantCoeff_apply, constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero] at h
  rw [h, sub_eq_zero, ← constantCoeff_apply, map_natCast]

theorem zInt_coeff_one : (zInt p).coeff 1 = 1 - (p : ℤ) ^ (p - 1) := by

  have h1 : ghostComponent 1 (zInt p) = (p : ℤ) - (p : ℤ) ^ p := by
    rw [zInt, map_sub, map_natCast, ghostComponent_teichmuller, pow_one]
  have h2 : ghostComponent 1 (zInt p) = (zInt p).coeff 0 ^ p + (p : ℤ) * (zInt p).coeff 1 := by
    rw [ghostComponent_apply, wittPolynomial_one]
    simp [map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
    ring
  rw [zInt_coeff_zero, zero_pow hp.out.ne_zero, zero_add] at h2
  have h3 : (p : ℤ) * (zInt p).coeff 1 = (p : ℤ) * (1 - (p : ℤ) ^ (p - 1)) := by
    rw [← h2, h1, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]
  exact mul_left_cancel₀ (by exact_mod_cast hp.out.ne_zero) h3

variable {p}

theorem natCast_eq_teichmuller_add_verschiebung (B : Type) [CommRing B] :
    ∃ η : 𝕎 B, (p : 𝕎 B) = teichmuller p (p : B) + verschiebung η ∧ η.coeff 0 = 1 - (p : B) ^ (p - 1) := by
  let z : 𝕎 B := map (Int.castRingHom B) (zInt p)
  have hz : z = (p : 𝕎 B) - teichmuller p (p : B) := by
    simp only [z, zInt, map_sub, map_natCast, map_teichmuller, map_natCast]
  have hz0 : z.coeff 0 = 0 := by rw [map_coeff, zInt_coeff_zero, map_zero]
  refine ⟨z.shift 1, ?_, ?_⟩
  · rw [verschiebung_shift z 0 (fun i hi => by interval_cases i; exact hz0)]
    have : z.shift 0 = z := by ext n; rw [shift_coeff, zero_add]
    rw [this, hz, add_sub_cancel]
  · rw [shift_coeff, add_zero, map_coeff, zInt_coeff_one]
    simp

theorem eq_teichmuller_add_verschiebung {B : Type} [CommRing B] (w : 𝕎 B) :
    ∃ w' : 𝕎 B, w = teichmuller p (w.coeff 0) + verschiebung w' := by
  let z : 𝕎 B := w - teichmuller p (w.coeff 0)
  have hz0 : z.coeff 0 = 0 := by
    have h : constantCoeff z = constantCoeff w - constantCoeff (teichmuller p (w.coeff 0)) := by rw [map_sub]
    rw [constantCoeff_apply, constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero, sub_self] at h
    exact h
  refine ⟨z.shift 1, ?_⟩
  rw [verschiebung_shift z 0 (fun i hi => by interval_cases i; exact hz0)]
  have : z.shift 0 = z := by ext n; rw [shift_coeff, zero_add]
  rw [this, add_sub_cancel]

theorem frobenius_teichmuller_coeff_zero {B : Type} [CommRing B] (b : B) :
    (frobenius (teichmuller p b)).coeff 0 = b ^ p := by
  have h1 : ghostComponent 0 (frobenius (teichmuller p b)) = ghostComponent 1 (teichmuller p b) :=
    ghostComponent_frobenius 0 _
  rw [ghostComponent_teichmuller, pow_one, ghostComponent_apply, wittPolynomial_zero, MvPolynomial.aeval_X] at h1
  exact h1

section ModulePart

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {B : Type} [CommRing B] {j : CerednikDrinfeld.Zp2 p →+* B} (D : CerednikDrinfeld.GradedCartierModuleData p B j)

theorem fin2_add_one_add_one (i : Fin 2) : i + 1 + 1 = i := by fin_cases i <;> rfl

theorem fin2_ne_iff (i k : Fin 2) : k ≠ i ↔ k = i + 1 := by fin_cases i <;> fin_cases k <;> decide

theorem isUnit_one_sub_pow (j : CerednikDrinfeld.Zp2 p →+* B) : IsUnit (1 - (p : B) ^ (p - 1)) := by
  have h : IsUnit (1 - (p : CerednikDrinfeld.Zp2 p) ^ (p - 1)) := by
    apply isUnit_of_coeff_zero_ne_zero
    rw [← constantCoeff_apply, map_sub, map_one, map_pow, map_natCast, CharP.cast_eq_zero,
      zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt), sub_zero]
    exact one_ne_zero
  have := h.map j
  rwa [map_sub, map_one, map_pow, map_natCast] at this

theorem verschiebung_smul_mem_vRange (w : 𝕎 B) (x : D.M) : verschiebung w • x ∈ D.vRange := by
  rw [← D.verschiebung_smul_frobenius]
  exact ⟨_, rfl⟩

theorem smul_sub_teichmuller_smul_mem_vRange (w : 𝕎 B) (x : D.M) :
    w • x - teichmuller p (w.coeff 0) • x ∈ D.vRange := by
  obtain ⟨w', hw⟩ := eq_teichmuller_add_verschiebung w
  have : w • x = teichmuller p (w.coeff 0) • x + verschiebung w' • x := by
    conv_lhs => rw [hw]
    rw [add_smul]
  rw [this, add_sub_cancel_left]
  exact verschiebung_smul_mem_vRange D w' x

theorem main (hD : D.IsSpecialCartierModule) (x : D.M) : D.frobenius x ∈ LinearMap.range D.lambda := by
  classical
  obtain ⟨⟨γ, hγmem, hγ⟩, -⟩ := hD

  let T : (Fin 2 → B) → D.M := fun c => ∑ i : Fin 2, teichmuller p (c i) • γ i
  have hT : ∀ c, T c = teichmuller p (c 0) • γ 0 + teichmuller p (c 1) • γ 1 := fun c => Fin.sum_univ_two _
  let S : Submodule (𝕎 B) D.M := LinearMap.range D.lambda
  have hPiS : ∀ m, D.varpi m ∈ S := fun m => ⟨D.nMk (m, 0), by rw [lambda_nMk, map_zero, add_zero]⟩
  have hVS : ∀ m, D.verschiebung m ∈ S := fun m => ⟨D.nMk (0, m), by rw [lambda_nMk, map_zero, zero_add]⟩
  have hVMS : D.vRange ≤ S := fun y ⟨m, hm⟩ => hm ▸ hVS m

  have uniq : ∀ (c c' : Fin 2 → B) (y y' : D.M), T c + D.verschiebung y = T c' + D.verschiebung y' → c = c' ∧ y = y' := by
    intro c c' y y' h
    have := (hγ (T c + D.verschiebung y)).unique (y₁ := (c, y)) (y₂ := (c', y')) rfl h
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hT0 : T 0 = 0 := by simp [T, teichmuller_zero]
  have Vinj : ∀ y y' : D.M, D.verschiebung y = D.verschiebung y' → y = y' := by
    intro y y' h
    exact (uniq 0 0 y y' (by rw [h])).2

  have decomp : ∀ y : D.M, ∃ y₀ ∈ D.piece 0, ∃ y₁ ∈ D.piece 1, y = y₀ + y₁ := by
    intro y
    have : y ∈ D.piece 0 ⊔ D.piece 1 := by rw [D.isCompl_piece.sup_eq_top]; trivial
    obtain ⟨y₀, h₀, y₁, h₁, h⟩ := Submodule.mem_sup.1 this
    exact ⟨y₀, h₀, y₁, h₁, h.symm⟩
  have disj : ∀ z : D.M, z ∈ D.piece 0 → z ∈ D.piece 1 → z = 0 := fun z h0 h1 =>
    (Submodule.disjoint_def.1 D.isCompl_piece.disjoint) z h0 h1

  have hTsingle : ∀ (k : Fin 2) (b : B), T (Pi.single k b) = teichmuller p b • γ k := by
    intro k b; fin_cases k <;> simp [hT, teichmuller_zero]

  have graded : ∀ (k : Fin 2) (c : Fin 2 → B) (y : D.M), T c + D.verschiebung y ∈ D.piece k →
      c (k + 1) = 0 ∧ y ∈ D.piece (k + 1) := by
    intro k c y hx
    obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := decomp y

    fin_cases k
    ·
      have hA : teichmuller p (c 0) • γ 0 + D.verschiebung y₁ ∈ D.piece 0 :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ (hγmem 0)) (by simpa using D.verschiebung_mem 1 y₁ hy₁)
      have hA' : teichmuller p (c 1) • γ 1 + D.verschiebung y₀ ∈ D.piece 1 :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ (hγmem 1)) (D.verschiebung_mem 0 y₀ hy₀)
      have hsum : T c + D.verschiebung (y₀ + y₁) =
          (teichmuller p (c 0) • γ 0 + D.verschiebung y₁) + (teichmuller p (c 1) • γ 1 + D.verschiebung y₀) := by
        rw [hT, map_add]; abel
      have hzero : teichmuller p (c 1) • γ 1 + D.verschiebung y₀ = 0 := by
        apply disj _ _ hA'
        have : teichmuller p (c 1) • γ 1 + D.verschiebung y₀ = (T c + D.verschiebung (y₀ + y₁)) - (teichmuller p (c 0) • γ 0 + D.verschiebung y₁) := by
          rw [hsum]; abel
        rw [this]; exact Submodule.sub_mem _ hx hA
      have := uniq (Pi.single 1 (c 1)) 0 y₀ 0 (by rw [hTsingle, hT0, map_zero, zero_add]; exact hzero)
      refine ⟨by simpa using congrFun this.1 1, ?_⟩
      rw [this.2, zero_add]; exact hy₁
    · have hA : teichmuller p (c 1) • γ 1 + D.verschiebung y₀ ∈ D.piece 1 :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ (hγmem 1)) (D.verschiebung_mem 0 y₀ hy₀)
      have hA' : teichmuller p (c 0) • γ 0 + D.verschiebung y₁ ∈ D.piece 0 :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ (hγmem 0)) (by simpa using D.verschiebung_mem 1 y₁ hy₁)
      have hsum : T c + D.verschiebung (y₀ + y₁) =
          (teichmuller p (c 1) • γ 1 + D.verschiebung y₀) + (teichmuller p (c 0) • γ 0 + D.verschiebung y₁) := by
        rw [hT, map_add]; abel
      have hzero : teichmuller p (c 0) • γ 0 + D.verschiebung y₁ = 0 := by
        apply disj _ hA'
        have : teichmuller p (c 0) • γ 0 + D.verschiebung y₁ = (T c + D.verschiebung (y₀ + y₁)) - (teichmuller p (c 1) • γ 1 + D.verschiebung y₀) := by
          rw [hsum]; abel
        rw [this]; exact Submodule.sub_mem _ hx hA
      have := uniq (Pi.single 0 (c 0)) 0 y₁ 0 (by rw [hTsingle, hT0, map_zero, zero_add]; exact hzero)
      refine ⟨by simpa using congrFun this.1 0, ?_⟩
      rw [this.2, add_zero]; simpa using hy₀

  have vgraded : ∀ (k : Fin 2) (h : D.M), D.verschiebung h ∈ D.piece k → h ∈ D.piece (k + 1) := by
    intro k h hh
    have := graded k 0 h (by rwa [hT0, zero_add])
    exact this.2

  have stepA : ∀ i : Fin 2, ∃ (α : B) (h : D.M), D.varpi (γ i) = teichmuller p α • γ (i + 1) + D.verschiebung h ∧ h ∈ D.piece i := by
    intro i
    obtain ⟨⟨c, h⟩, hch, -⟩ := hγ (D.varpi (γ i))
    have hmem : T c + D.verschiebung h ∈ D.piece (i + 1) := hch ▸ D.varpi_mem i _ (hγmem i)
    obtain ⟨hc, hh⟩ := graded (i + 1) c h hmem
    rw [fin2_add_one_add_one] at hc hh
    refine ⟨c (i + 1), h, ?_, hh⟩
    rw [hch]
    show T c + D.verschiebung h = _
    rw [hT]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · rw [hc, teichmuller_zero, zero_smul, zero_add]; rfl
    · rw [hc, teichmuller_zero, zero_smul, add_zero]; rfl
  choose α hh hA hhmem using stepA

  obtain ⟨η, hη, hη0⟩ := natCast_eq_teichmuller_add_verschiebung (p := p) B
  have hpsmul : ∀ y : D.M, (p : ℕ) • y = teichmuller p (p : B) • y + D.verschiebung (η • D.frobenius y) := by
    intro y
    rw [← Nat.cast_smul_eq_nsmul (𝕎 B), hη, add_smul, D.verschiebung_smul_frobenius]

  have stepB : ∀ i : Fin 2, η • D.frobenius (γ i) =
      frobenius (teichmuller p (α i)) • hh (i + 1) + D.varpi (hh i) ∧ α i * α (i + 1) = (p : B) := by
    intro i
    have h1 : (p : ℕ) • γ i = D.varpi (D.varpi (γ i)) := (D.varpi_varpi (γ i)).symm
    have h2 : D.varpi (D.varpi (γ i)) =
        teichmuller p (α i * α (i + 1)) • γ i + D.verschiebung (frobenius (teichmuller p (α i)) • hh (i + 1) + D.varpi (hh i)) := by
      conv_lhs => rw [hA i]
      rw [map_add, D.varpi_smul, D.varpi_verschiebung, hA (i + 1), fin2_add_one_add_one, smul_add, smul_smul,
        ← map_mul, D.smul_verschiebung, map_add, add_assoc]
    have h3 := hpsmul (γ i)
    rw [h1, h2] at h3

    have h4 := uniq (Pi.single i (α i * α (i + 1))) (Pi.single i (p : B))
      (frobenius (teichmuller p (α i)) • hh (i + 1) + D.varpi (hh i)) (η • D.frobenius (γ i))
      (by rw [hTsingle, hTsingle]; exact h3)
    refine ⟨h4.2.symm, ?_⟩
    have := congrFun h4.1 i
    simpa using this

  have hη0u : IsUnit (η.coeff 0) := by rw [hη0]; exact isUnit_one_sub_pow (p := p) j
  have stepC : ∀ i : Fin 2, D.frobenius (γ i) ∈ S := by
    intro i

    have hmem1 : η • D.frobenius (γ i) ∈ S := by
      rw [(stepB i).1]
      refine Submodule.add_mem _ ?_ (hPiS _)

      obtain ⟨⟨d, y⟩, hdy, -⟩ := hγ (hh (i + 1))
      have hd : d i = 0 := by
        have := (graded (i + 1) d y (hdy ▸ hhmem (i + 1))).1
        rwa [fin2_add_one_add_one] at this
      have hdy' : hh (i + 1) = teichmuller p (d (i + 1)) • γ (i + 1) + D.verschiebung y := by
        rw [hdy]; show T d + D.verschiebung y = _; rw [hT]
        have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
        rcases hi with rfl | rfl
        · rw [hd, teichmuller_zero, zero_smul, zero_add]; rfl
        · rw [hd, teichmuller_zero, zero_smul, add_zero]; rfl
      rw [hdy', smul_add, D.smul_verschiebung]
      refine Submodule.add_mem _ ?_ (hVS _)

      have hmod := smul_sub_teichmuller_smul_mem_vRange D (frobenius (teichmuller p (α i))) (teichmuller p (d (i + 1)) • γ (i + 1))
      rw [frobenius_teichmuller_coeff_zero] at hmod
      have hmain : teichmuller p (α i ^ p) • (teichmuller p (d (i + 1)) • γ (i + 1)) ∈ S := by
        have : teichmuller p (α i ^ p) • (teichmuller p (d (i + 1)) • γ (i + 1)) =
            teichmuller p (α i ^ (p - 1) * d (i + 1)) • (D.varpi (γ i) - D.verschiebung (hh i)) := by
          rw [hA i, add_sub_cancel_right, smul_smul, smul_smul, ← map_mul, ← map_mul]
          congr 1; congr 1
          rw [mul_right_comm, ← pow_succ, Nat.sub_add_cancel hp.out.one_le]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hPiS _) (hVS _))
      have := Submodule.add_mem _ (hVMS hmod) hmain
      rwa [sub_add_cancel] at this

    have hmem2 : teichmuller p (η.coeff 0) • D.frobenius (γ i) ∈ S := by
      have := Submodule.sub_mem _ hmem1 (hVMS (smul_sub_teichmuller_smul_mem_vRange D η (D.frobenius (γ i))))
      rwa [sub_sub_cancel] at this
    obtain ⟨u, hu⟩ := hη0u
    have : D.frobenius (γ i) = teichmuller p (↑u⁻¹ : B) • (teichmuller p (η.coeff 0) • D.frobenius (γ i)) := by
      rw [smul_smul, ← map_mul, ← hu, Units.inv_mul, (teichmuller p).map_one, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem2

  obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ x
  rw [hcy]
  show D.frobenius (T c + D.verschiebung y) ∈ S
  rw [map_add, D.frobenius_verschiebung, hT, map_add, D.frobenius_smul, D.frobenius_smul, ← D.varpi_varpi]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (stepC 0)) (Submodule.smul_mem _ _ (stepC 1))) (hPiS _)

end ModulePart

end FSubPiVAux

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule) (x : D.M) :
    D.frobenius x ∈ LinearMap.range D.lambda := FSubPiVAux.main (p := p) D hD x

end S_CerednikDrinfeld_GradedCartierModuleData_frobenius_mem_range_lambda_of_isSpecialCartierModule
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_frobenius_mem_range_lambda_of_isSpecialCartierModule (solution)
