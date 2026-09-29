-- Prove2me | solution 1 for CohCarrier.exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_sq_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/89cd1e19-f1cb-5cf5-9709-d0cda92ef173

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CohCarrier_heckeT_comb_eq_zero
import Theorems.Thm_CohCarrier_iDeg_comp
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_sq_of_prime
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace OccupancySol

open CohCarrier IharaLemma
open scoped IsMulCommutative MatrixGroups
open CongruenceSubgroup

section DiamondTop

variable (M : ℕ) [NeZero M] (A : Type) [AddCommGroup A]

theorem diamondRaw_top_eq_self (σ : Gamma0 M) (φ : H1 M ⊤ A) : diamondRaw M ⊤ A σ φ = φ := by
  have hσ : (σ : SL(2, ℤ)) ∈ GammaH M ⊤ := mem_GammaH_iff.mpr ⟨σ.2, Subgroup.mem_top _⟩
  set κ : ↥(GammaH M ⊤) := ⟨(σ : SL(2, ℤ)), hσ⟩ with hκ
  refine AddMonoidHom.ext fun a => ?_
  show φ (Additive.ofMul (conjHom M ⊤ σ (Additive.toMul a))) = φ a
  have hconj : conjHom M ⊤ σ (Additive.toMul a) = κ * Additive.toMul a * κ⁻¹ := by
    apply Subtype.ext
    simp [conjHom, hκ]
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, ofMul_toMul]
  abel

theorem diamondL_top_eq_one (𝒪 : Type) [CommRing 𝒪] (d : (ZMod M)ˣ) :
    diamondL M ⊤ 𝒪 d = 1 := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective M d
  refine LinearMap.ext fun φ => ?_
  rw [diamondL_eq_diamondRaw M ⊤ 𝒪 d σ hσ φ, diamondRaw_top_eq_self]
  rfl

end DiamondTop

section Hecke

variable (M : ℕ) [NeZero M] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  (hcomm : ∀ g g' : Gen M S,
      opFamily M ⊤ S 𝒪 g * opFamily M ⊤ S 𝒪 g' = opFamily M ⊤ S 𝒪 g' * opFamily M ⊤ S 𝒪 g)
  (θbar : Gen M S → k)

local notation3 "𝕋" => (CohCarrier.hdata M ⊤ S 𝒪 k hcomm θbar).opSubalgebra

noncomputable def gOp (g : Gen M S) : ↥𝕋 :=
  ⟨(hdata M ⊤ S 𝒪 k hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩

@[scoped simp] theorem coe_gOp (g : Gen M S) :
    ((gOp M S 𝒪 k hcomm θbar g : ↥𝕋) : Module.End 𝒪 (H1 M ⊤ 𝒪)) = opFamily M ⊤ S 𝒪 g := rfl

theorem subalg_smul_def (b : ↥𝕋) (m : H1 M ⊤ 𝒪) :
    b • m = (b : Module.End 𝒪 (H1 M ⊤ 𝒪)) m := rfl

theorem gOp_dia_eq_one (d : (ZMod M)ˣ) : gOp M S 𝒪 k hcomm θbar (Gen.dia d) = 1 := by
  apply Subtype.ext
  rw [coe_gOp, Subalgebra.coe_one]
  exact diamondL_top_eq_one M 𝒪 d

noncomputable def freeToT : MvPolynomial (Gen M S) 𝒪 →ₐ[𝒪] ↥𝕋 :=
  MvPolynomial.aeval (gOp M S 𝒪 k hcomm θbar)

theorem freeToT_X (g : Gen M S) :
    freeToT M S 𝒪 k hcomm θbar (MvPolynomial.X g) = gOp M S 𝒪 k hcomm θbar g := by
  simp [freeToT]

theorem freeToT_C (r : 𝒪) : freeToT M S 𝒪 k hcomm θbar (MvPolynomial.C r) = algebraMap 𝒪 ↥𝕋 r :=
  MvPolynomial.aeval_C _ r

theorem surjective_of_forall_gOp_mem_range {G : Type} (ψ : MvPolynomial G 𝒪 →ₐ[𝒪] ↥𝕋)
    (hψ : ∀ g : Gen M S, ∃ f, ψ f = gOp M S 𝒪 k hcomm θbar g) : Function.Surjective ψ := by
  intro x
  obtain ⟨x, hx⟩ := x
  refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
  · rintro _ ⟨g, rfl⟩
    obtain ⟨f, hf⟩ := hψ g
    exact ⟨f, hf⟩
  · intro r
    exact ⟨algebraMap 𝒪 _ r, by rw [AlgHom.commutes]; rfl⟩
  · rintro x y hx hy ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f + g, by rw [map_add, hf, hg]; rfl⟩
  · rintro x y hx hy ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f * g, by rw [map_mul, hf, hg]; rfl⟩

theorem freeToT_surjective : Function.Surjective (freeToT M S 𝒪 k hcomm θbar) :=
  surjective_of_forall_gOp_mem_range M S 𝒪 k hcomm θbar _ fun g =>
    ⟨MvPolynomial.X g, freeToT_X M S 𝒪 k hcomm θbar g⟩

variable (Sp : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdata M ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n)

noncomputable def toCornerAlg : ↥𝕋 →ₐ[𝒪] Sp.CornerRing i₀ where
  toFun := Sp.toCornerRing i₀
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' _ := rfl

@[scoped simp] theorem toCornerAlg_apply (b : ↥𝕋) :
    toCornerAlg M S 𝒪 k hcomm θbar Sp i₀ b = Sp.toCornerRing i₀ b := rfl

theorem toCornerRing_eq_zero_of_forall_smul_eq_zero (b : ↥𝕋)
    (h : ∀ v : H1 M ⊤ 𝒪, v ∈ IharaLemma.cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i₀) → b • v = 0) :
    Sp.toCornerRing i₀ b = 0 := by
  apply Subtype.ext
  rw [IdempotentSplitting.coe_toCornerRing]
  show Sp.e i₀ * b * Sp.e i₀ = (0 : ↥𝕋)
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_zero]
  refine LinearMap.ext fun φ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.zero_apply]
  have hmem : (Sp.e i₀ : Module.End 𝒪 (H1 M ⊤ 𝒪)) φ ∈
      IharaLemma.cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i₀) := ⟨φ, rfl⟩
  have h0 := h _ hmem
  rw [subalg_smul_def] at h0
  rw [h0, map_zero]

theorem gOp_T_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) [NeZero ℓ] (v : H1 M ⊤ 𝒪) :
    (gOp M S 𝒪 k hcomm θbar (Gen.T ℓ hℓ hℓS hℓM)) • v = heckeT M ⊤ ℓ 𝒪 v := rfl

theorem gOp_U_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) [NeZero ℓ] (v : H1 M ⊤ 𝒪) :
    (gOp M S 𝒪 k hcomm θbar (Gen.U ℓ hℓ hℓM)) • v = heckeT M ⊤ ℓ 𝒪 v := rfl

theorem gOp_dia_smul (d : (ZMod M)ˣ) (v : H1 M ⊤ 𝒪) :
    (gOp M S 𝒪 k hcomm θbar (Gen.dia d)) • v = v := by
  rw [gOp_dia_eq_one, one_smul]

theorem algebraMap_smul_eq (r : 𝒪) (v : H1 M ⊤ 𝒪) : (algebraMap 𝒪 ↥𝕋 r) • v = r • v :=
  algebraMap_smul _ r v

end Hecke

section CornerPoint

variable {B : Type} [CommRing B] (Sp : IdempotentSplitting B) (i : Fin Sp.n)
  (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B] {k : Type} [Field k] [Algebra 𝒪 k]

theorem exists_algHom_cornerRing_of_ker_eq (χ : B →ₐ[𝒪] k)
    (hker : RingHom.ker χ = Sp.𝔪 i) :
    ∃ π : Sp.CornerRing i →ₐ[𝒪] k, ∀ b : B, π (Sp.toCornerRing i b) = χ b := by
  have hunit : ∀ y : (Sp.𝔪 i).primeCompl, IsUnit ((χ : B →+* k) y) := fun y => by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have hy : (y : B) ∉ Sp.𝔪 i := y.2
    exact hy (hker.le ((RingHom.mem_ker).mpr h0))
  let π₀ : Sp.CornerRing i →+* k := IsLocalization.lift (M := (Sp.𝔪 i).primeCompl) hunit
  have hπ₀ : ∀ b : B, π₀ (Sp.toCornerRing i b) = χ b := fun b =>
    IsLocalization.lift_eq (M := (Sp.𝔪 i).primeCompl) hunit b
  refine ⟨{ π₀ with commutes' := fun r => ?_ }, fun b => hπ₀ b⟩
  show π₀ (Sp.toCornerRing i (algebraMap 𝒪 B r)) = algebraMap 𝒪 k r
  rw [hπ₀, AlgHom.commutes]

theorem exists_algHom_comp_eq_of_surjective {R A B' C : Type} [CommRing R] [CommRing A]
    [Algebra R A] [Semiring B'] [Algebra R B'] [Semiring C] [Algebra R C]
    (f : A →ₐ[R] B') (hf : Function.Surjective f) (g : A →ₐ[R] C)
    (h : ∀ a, f a = 0 → g a = 0) : ∃ g' : B' →ₐ[R] C, ∀ a, g' (f a) = g a := by
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h a ((RingHom.mem_ker).mp ha))).comp
    (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom, fun a => ?_⟩
  rw [AlgHom.comp_apply]
  have hs : (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom (f a) =
      Ideal.Quotient.mk (RingHom.ker f) a :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply hf a
  rw [hs]
  rfl

end CornerPoint

section Levels

theorem levelLE_top {M M' d : ℕ} (hM : M ∣ M') (hd : d ∣ M' / M) :
    LevelLE M M' (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod M')ˣ) d :=
  ⟨hM, hd, fun _ _ => Subgroup.mem_top _⟩

theorem iDeg'_congr_d {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
    {A : Type} [AddCommGroup A] {d d' : ℕ} (hd : d = d') [NeZero d] [NeZero d']
    (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d') (φ : H1 M H A) :
    iDeg' M M' H H' d A h φ = iDeg' M M' H H' d' A h' φ := by
  subst hd
  rfl

variable {N q : ℕ} [NeZero N] [NeZero q] (hqp : q.Prime) (hqN : ¬ q ∣ N) {A : Type} [AddCommGroup A]

theorem levelLE_one_Nq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1 :=
  levelLE_top (dvd_mul_right N q) (one_dvd _)

theorem levelLE_q_Nq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q :=
  levelLE_top (dvd_mul_right N q) (by rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne N))])

theorem levelLE_one_Nq_Nq2 :
    LevelLE (N * q) (N * q ^ 2) (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1 :=
  levelLE_top (by rw [pow_two, ← mul_assoc]; exact dvd_mul_right _ q) (one_dvd _)

theorem levelLE_q_Nq_Nq2 :
    LevelLE (N * q) (N * q ^ 2) (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q :=
  levelLE_top (by rw [pow_two, ← mul_assoc]; exact dvd_mul_right _ q) (by
    rw [pow_two, ← mul_assoc, Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne (N * q)))])

theorem levelLE_N_Nq2 (d : ℕ) (hd : d ∣ q * q) :
    LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) d :=
  levelLE_top (dvd_mul_right N _) (by
    rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N)), pow_two])

include hqp hqN in

theorem heckeT_comb_eq_zero_gen (M₃ : ℕ) [NeZero M₃] (e : N * q * q = M₃)
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (h₁' : LevelLE (N * q) M₃ (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) 1)
    (hq' : LevelLE (N * q) M₃ (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) q)
    (φ : H1 N ⊤ A) :
    heckeT M₃ ⊤ q A
        (q • iDeg' (N * q) M₃ ⊤ ⊤ 1 A h₁' (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ)
          - iDeg' (N * q) M₃ ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ (heckeT N ⊤ q A φ))
          + iDeg' (N * q) M₃ ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ q A hq φ)) = 0 := by
  subst e
  exact heckeT_comb_eq_zero h₁ hqp hqN hq h₁' hq' φ

include hqp hqN in

theorem heckeT_levelRaisingComb_eq_zero
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))
    (φ : H1 N ⊤ A) :
    heckeT (N * q ^ 2) ⊤ q A
        (q • iDeg' N (N * q ^ 2) ⊤ ⊤ 1 A h1 φ
          - iDeg' N (N * q ^ 2) ⊤ ⊤ q A hq' (heckeT N ⊤ q A φ)
          + iDeg' N (N * q ^ 2) ⊤ ⊤ (q ^ 2) A hq2 φ) = 0 := by
  have h := heckeT_comb_eq_zero_gen hqp hqN (A := A) (N * q ^ 2) (by ring)
    levelLE_one_Nq levelLE_q_Nq levelLE_one_Nq_Nq2 levelLE_q_Nq_Nq2 φ
  haveI : NeZero (1 * 1) := ⟨by norm_num⟩
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact NeZero.ne q⟩
  haveI : NeZero (q * q) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne q)⟩
  rw [← iDeg_comp levelLE_one_Nq levelLE_one_Nq_Nq2 (levelLE_N_Nq2 (1 * 1) (by simp)),
    ← iDeg_comp levelLE_one_Nq levelLE_q_Nq_Nq2 (levelLE_N_Nq2 (1 * q) (by simp)),
    ← iDeg_comp levelLE_q_Nq levelLE_q_Nq_Nq2 (levelLE_N_Nq2 (q * q) dvd_rfl)] at h
  rw [iDeg'_congr_d (one_mul 1).symm h1 (levelLE_N_Nq2 (1 * 1) (by simp)),
    iDeg'_congr_d (one_mul q).symm hq' (levelLE_N_Nq2 (1 * q) (by simp)),
    iDeg'_congr_d (pow_two q) hq2 (levelLE_N_Nq2 (q * q) dvd_rfl)]
  exact h

end Levels

section TwoLevels

theorem heckeT_smul (M : ℕ) (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪] (ℓ : ℕ) [NeZero ℓ]
    (r : 𝒪) (x : H1 M H 𝒪) : heckeT M H ℓ 𝒪 (r • x) = r • heckeT M H ℓ 𝒪 x :=
  (heckeTL M H 𝒪 ℓ).map_smul r x

variable (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
  (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
  (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
  (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))
  (S : Set ℕ) (hqS : q ∈ S) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  (hcomm : ∀ g g' : Gen N S,
      opFamily N ⊤ S 𝒪 g * opFamily N ⊤ S 𝒪 g' = opFamily N ⊤ S 𝒪 g' * opFamily N ⊤ S 𝒪 g)
  (hcomm' : ∀ g g' : Gen (N * q ^ 2) S,
      opFamily (N * q ^ 2) ⊤ S 𝒪 g * opFamily (N * q ^ 2) ⊤ S 𝒪 g' =
        opFamily (N * q ^ 2) ⊤ S 𝒪 g' * opFamily (N * q ^ 2) ⊤ S 𝒪 g)
  (θbar : Gen N S → k) (θbar' : Gen (N * q ^ 2) S → k)

local notation3 "𝕋" => (CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra
local notation3 "𝕋'" => (CohCarrier.hdata (N * q ^ 2) ⊤ S 𝒪 k hcomm' θbar').opSubalgebra

include hq in
theorem eq_of_dvd_mul_sq {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ¬ ℓ ∣ N) : q = ℓ := by
  rcases (Nat.Prime.dvd_mul hℓ).mp hℓM with h | h
  · exact absurd h hℓN
  · exact ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp (hℓ.dvd_of_dvd_pow h)).symm

noncomputable def τ : Gen (N * q ^ 2) S → ↥𝕋
  | .T ℓ hℓ hℓS hℓM => gOp N S 𝒪 k hcomm θbar (.T ℓ hℓ hℓS (fun h => hℓM (h.mul_right _)))
  | .U ℓ hℓ _ => if h : ℓ ∣ N then gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ h) else 0
  | .dia _ => 1

theorem τ_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q ^ 2) (hℓN : ¬ ℓ ∣ N) :
    τ N q S 𝒪 k hcomm θbar (.T ℓ hℓ hℓS hℓM) = gOp N S 𝒪 k hcomm θbar (.T ℓ hℓ hℓS hℓN) := rfl

theorem τ_U_of_dvd (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ℓ ∣ N) :
    τ N q S 𝒪 k hcomm θbar (.U ℓ hℓ hℓM) = gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ hℓN) := by
  show (if h : ℓ ∣ N then gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ h) else 0) = _
  rw [dif_pos hℓN]

theorem τ_U_of_not_dvd (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ¬ ℓ ∣ N) :
    τ N q S 𝒪 k hcomm θbar (.U ℓ hℓ hℓM) = 0 := by
  show (if h : ℓ ∣ N then gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ h) else 0) = _
  rw [dif_neg hℓN]

theorem τ_dia (d : (ZMod (N * q ^ 2))ˣ) : τ N q S 𝒪 k hcomm θbar (.dia d) = 1 := rfl

noncomputable def ψ : MvPolynomial (Gen (N * q ^ 2) S) 𝒪 →ₐ[𝒪] ↥𝕋 :=
  MvPolynomial.aeval (τ N q S 𝒪 k hcomm θbar)

theorem ψ_X (g : Gen (N * q ^ 2) S) :
    ψ N q S 𝒪 k hcomm θbar (MvPolynomial.X g) = τ N q S 𝒪 k hcomm θbar g := by
  simp [ψ]

theorem ψ_C (r : 𝒪) : ψ N q S 𝒪 k hcomm θbar (MvPolynomial.C r) = algebraMap 𝒪 ↥𝕋 r :=
  MvPolynomial.aeval_C _ r

variable (Sp : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] k)
  (hπk : ∀ g : Gen N S, πk (Sp.toCornerRing i₀
    ⟨(hdata N ⊤ S 𝒪 k hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
  (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q ^ 2),
    θbar' (Gen.T ℓ hℓ hℓS hℓM) = θbar (Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h (q ^ 2)))))
  (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ℓ ∣ N),
    θbar' (Gen.U ℓ hℓ hℓM) = θbar (Gen.U ℓ hℓ hℓN))
  (hθq : θbar' (Gen.U q hq (dvd_mul_of_dvd_right (dvd_pow_self q two_ne_zero) N)) = 0)
  (hθdia : ∀ d : (ZMod (N * q ^ 2))ˣ, θbar' (Gen.dia d) = 1)

include hπk in
theorem hπk_gOp (g : Gen N S) : πk (Sp.toCornerRing i₀ (gOp N S 𝒪 k hcomm θbar g)) = θbar g := hπk g

set_option maxHeartbeats 16000000 in
include hq hπk hθT hθU hθq hθdia in

theorem πk_τ_eq (g : Gen (N * q ^ 2) S) :
    πk (Sp.toCornerRing i₀ (τ N q S 𝒪 k hcomm θbar g)) = θbar' g := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    rw [τ_T N q S 𝒪 k hcomm θbar ℓ hℓ hℓS hℓM (fun h => hℓM (Dvd.dvd.mul_right h (q ^ 2))),
      hπk_gOp N S 𝒪 k hcomm θbar Sp i₀ πk hπk, hθT]
  | U ℓ hℓ hℓM =>
    by_cases h : ℓ ∣ N
    · rw [τ_U_of_dvd N q S 𝒪 k hcomm θbar ℓ hℓ hℓM h, hπk_gOp N S 𝒪 k hcomm θbar Sp i₀ πk hπk,
        hθU ℓ hℓ hℓM h]
    · have hz : θbar' (Gen.U ℓ hℓ hℓM) = 0 := by
        have key : ∀ (ℓ' : ℕ) (hℓ' : ℓ'.Prime) (hℓM' : ℓ' ∣ N * q ^ 2), q = ℓ' →
            θbar' (Gen.U ℓ' hℓ' hℓM') = 0 := by
          rintro ℓ' hℓ' hℓM' rfl
          exact hθq
        exact key ℓ hℓ hℓM (eq_of_dvd_mul_sq N q hq hℓ hℓM h)
      rw [τ_U_of_not_dvd N q S 𝒪 k hcomm θbar ℓ hℓ hℓM h, RingHom.map_zero, map_zero, hz]
  | dia d =>
    rw [τ_dia, RingHom.map_one, map_one, hθdia]

noncomputable def wL : H1 N ⊤ 𝒪 →ₗ[𝒪] H1 (N * q ^ 2) ⊤ 𝒪 :=
  (q : 𝒪) • iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
    - (iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (heckeTL N ⊤ 𝒪 q)
    + iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2

theorem wL_apply (v : H1 N ⊤ 𝒪) :
    wL N q h1 hq' hq2 𝒪 v = (q : 𝒪) • iDeg' N (N * q ^ 2) ⊤ ⊤ 1 𝒪 h1 v
      - iDeg' N (N * q ^ 2) ⊤ ⊤ q 𝒪 hq' (heckeT N ⊤ q 𝒪 v)
      + iDeg' N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 hq2 v := rfl

include hq hqN in

theorem wL_τ_smul (g : Gen (N * q ^ 2) S) (v : H1 N ⊤ 𝒪) :
    wL N q h1 hq' hq2 𝒪 ((τ N q S 𝒪 k hcomm θbar g) • v) =
      (gOp (N * q ^ 2) S 𝒪 k hcomm' θbar' g) • wL N q h1 hq' hq2 𝒪 v := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓq : ℓ ≠ q := fun h => hℓM (h ▸ dvd_mul_of_dvd_right (dvd_pow_self q two_ne_zero) N)
    have hcop : Nat.Coprime ℓ q := (Nat.coprime_primes hℓ hq).mpr hℓq
    show wL N q h1 hq' hq2 𝒪 (heckeT N ⊤ ℓ 𝒪 v) = heckeT (N * q ^ 2) ⊤ ℓ 𝒪 (wL N q h1 hq' hq2 𝒪 v)
    rw [wL_apply, wL_apply, map_add, map_sub, heckeT_smul,
      heckeT_comm_of_prime N ⊤ q ℓ hq hcop.symm v,
      iDeg_heckeT_comm_of_coprime h1 (Nat.coprime_one_right ℓ) hℓ hℓM,
      iDeg_heckeT_comm_of_coprime hq' hcop hℓ hℓM,
      iDeg_heckeT_comm_of_coprime hq2 (Nat.Coprime.pow_right 2 hcop) hℓ hℓM]
  | U ℓ hℓ hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    by_cases h : ℓ ∣ N
    · have hℓq : ℓ ≠ q := fun h' => hqN (h' ▸ h)
      have hcop : Nat.Coprime ℓ q := (Nat.coprime_primes hℓ hq).mpr hℓq
      rw [τ_U_of_dvd N q S 𝒪 k hcomm θbar ℓ hℓ hℓM h]
      show wL N q h1 hq' hq2 𝒪 (heckeT N ⊤ ℓ 𝒪 v) = heckeT (N * q ^ 2) ⊤ ℓ 𝒪 (wL N q h1 hq' hq2 𝒪 v)
      rw [wL_apply, wL_apply, map_add, map_sub, heckeT_smul,
        heckeT_comm_of_prime N ⊤ q ℓ hq hcop.symm v,
        iDeg_heckeT_comm_of_dvd h1 (Nat.coprime_one_right ℓ) h,
        iDeg_heckeT_comm_of_dvd hq' hcop h,
        iDeg_heckeT_comm_of_dvd hq2 (Nat.Coprime.pow_right 2 hcop) h]
    · have key : ∀ (ℓ' : ℕ) (_ : NeZero ℓ'), q = ℓ' →
          heckeT (N * q ^ 2) ⊤ ℓ' 𝒪 (wL N q h1 hq' hq2 𝒪 v) = 0 := by
        rintro ℓ' _ rfl
        rw [wL_apply, Nat.cast_smul_eq_nsmul, heckeT_levelRaisingComb_eq_zero hq hqN h1 hq' hq2 v]
      rw [τ_U_of_not_dvd N q S 𝒪 k hcomm θbar ℓ hℓ hℓM h, zero_smul, map_zero]
      exact (key ℓ inferInstance (eq_of_dvd_mul_sq N q hq hℓ hℓM h)).symm
  | dia d =>
    rw [gOp_dia_smul]
    show wL N q h1 hq' hq2 𝒪 ((1 : ↥𝕋) • v) = _
    rw [one_smul]

set_option maxHeartbeats 16000000 in
include hq hqN in

theorem wL_ψ_smul (f : MvPolynomial (Gen (N * q ^ 2) S) 𝒪) (v : H1 N ⊤ 𝒪) :
    wL N q h1 hq' hq2 𝒪 ((ψ N q S 𝒪 k hcomm θbar f) • v) =
      (freeToT (N * q ^ 2) S 𝒪 k hcomm' θbar' f) • wL N q h1 hq' hq2 𝒪 v := by
  induction f using MvPolynomial.induction_on generalizing v with
  | C r =>
    rw [ψ_C, freeToT_C, algebraMap_smul_eq, algebraMap_smul_eq, LinearMap.map_smul]
  | add p p' hp hp' =>
    rw [map_add, map_add, add_smul, add_smul, LinearMap.map_add, hp, hp']
  | mul_X p g hp =>
    rw [map_mul, map_mul, ψ_X, freeToT_X, subalg_smul_def, Subalgebra.coe_mul, Module.End.mul_apply,
      ← subalg_smul_def, ← subalg_smul_def, hp, wL_τ_smul N q hq hqN, subalg_smul_def,
      subalg_smul_def _ _ _ _ _ _ (_ * _), Subalgebra.coe_mul, Module.End.mul_apply]
    rfl

variable
  (hinj : ∀ φ : H1 N ⊤ 𝒪, φ ∈ IharaLemma.cornerSubmodule (M := H1 N ⊤ 𝒪) (Sp.e i₀) →
    wL N q h1 hq' hq2 𝒪 φ = 0 → φ = 0)

noncomputable def χ : MvPolynomial (Gen (N * q ^ 2) S) 𝒪 →ₐ[𝒪] k :=
  (πk.comp (toCornerAlg N S 𝒪 k hcomm θbar Sp i₀)).comp (ψ N q S 𝒪 k hcomm θbar)

theorem χ_apply (f : MvPolynomial (Gen (N * q ^ 2) S) 𝒪) :
    χ N q S 𝒪 k hcomm θbar Sp i₀ πk f = πk (Sp.toCornerRing i₀ (ψ N q S 𝒪 k hcomm θbar f)) := rfl

include hq hπk hθT hθU hθq hθdia in
theorem χ_X (g : Gen (N * q ^ 2) S) :
    χ N q S 𝒪 k hcomm θbar Sp i₀ πk (MvPolynomial.X g) = θbar' g := by
  rw [χ_apply, ψ_X]
  exact πk_τ_eq N q hq S 𝒪 k hcomm θbar θbar' Sp i₀ πk hπk hθT hθU hθq hθdia g

set_option maxHeartbeats 16000000 in
include hq hqN hinj in

theorem χ_eq_zero_of_freeToT_eq_zero (f : MvPolynomial (Gen (N * q ^ 2) S) 𝒪)
    (hf : freeToT (N * q ^ 2) S 𝒪 k hcomm' θbar' f = 0) :
    χ N q S 𝒪 k hcomm θbar Sp i₀ πk f = 0 := by
  rw [χ_apply]
  have hkill : ∀ v : H1 N ⊤ 𝒪, v ∈ IharaLemma.cornerSubmodule (M := H1 N ⊤ 𝒪) (Sp.e i₀) →
      (ψ N q S 𝒪 k hcomm θbar f) • v = 0 := by
    intro v hv
    refine hinj _ (Submodule.smul_mem _ _ hv) ?_
    rw [wL_ψ_smul N q hq hqN h1 hq' hq2 S 𝒪 k hcomm hcomm' θbar θbar' f v, hf, zero_smul]
  rw [toCornerRing_eq_zero_of_forall_smul_eq_zero N S 𝒪 k hcomm θbar Sp i₀ _ hkill, map_zero]

include hq hqN hπk hθT hθU hθq hθdia hinj in

theorem exists_residualPoint :
    ∃ ρ : ↥𝕋' →ₐ[𝒪] k,
      ∀ g : Gen (N * q ^ 2) S, ρ (gOp (N * q ^ 2) S 𝒪 k hcomm' θbar' g) = θbar' g := by
  obtain ⟨ρ, hρ⟩ := exists_algHom_comp_eq_of_surjective (freeToT (N * q ^ 2) S 𝒪 k hcomm' θbar')
    (freeToT_surjective (N * q ^ 2) S 𝒪 k hcomm' θbar') (χ N q S 𝒪 k hcomm θbar Sp i₀ πk)
    (χ_eq_zero_of_freeToT_eq_zero N q hq hqN h1 hq' hq2 S 𝒪 k hcomm hcomm' θbar θbar' Sp i₀ πk
      hinj)
  refine ⟨ρ, fun g => ?_⟩
  rw [← freeToT_X, hρ]
  exact χ_X N q hq S 𝒪 k hcomm θbar θbar' Sp i₀ πk hπk hθT hθU hθq hθdia g

include hq hqN hπk hθT hθU hθq hθdia hinj in

theorem exists_index_algHom (hk : Function.Surjective (algebraMap 𝒪 k))
    (Sp' : IharaLemma.IdempotentSplitting ↥𝕋') :
    ∃ (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] k),
      ∀ g : Gen (N * q ^ 2) S,
        πk' (Sp'.toCornerRing i₀' (gOp (N * q ^ 2) S 𝒪 k hcomm' θbar' g)) = θbar' g := by
  obtain ⟨ρ, hρ⟩ := exists_residualPoint N q hq hqN h1 hq' hq2 S 𝒪 k hcomm hcomm' θbar θbar' Sp i₀
    πk hπk hθT hθU hθq hθdia hinj
  have hsurj : Function.Surjective ρ := fun x => by
    obtain ⟨r, rfl⟩ := hk x
    exact ⟨algebraMap 𝒪 _ r, AlgHom.commutes ρ r⟩
  haveI hmax : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective ρ hsurj
  obtain ⟨i₀', hi₀'⟩ := Sp'.exists_eq _ hmax
  obtain ⟨πk', hπk'⟩ := exists_algHom_cornerRing_of_ker_eq Sp' i₀' 𝒪 ρ hi₀'.symm
  exact ⟨i₀', πk', fun g => by rw [hπk', hρ]⟩

end TwoLevels

end OccupancySol
p2m_reactivate "P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_sq_of_prime.OccupancySol"

set_option maxHeartbeats 16000000 in
open scoped IsMulCommutative in
theorem solution
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))
    (S : Set ℕ) (hqS : q ∈ S)
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (hcomm : ∀ g g' : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 g' =
        CohCarrier.opFamily N ⊤ S 𝒪 g' * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (hcomm' : ∀ g g' : CohCarrier.Gen (N * q ^ 2) S,
      CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g * CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g' =
        CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g' * CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → IsLocalRing.ResidueField 𝒪)
    (θbar' : CohCarrier.Gen (N * q ^ 2) S → IsLocalRing.ResidueField 𝒪)

    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q ^ 2),
      θbar' (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) =
        θbar (CohCarrier.Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h (q ^ 2)))))
    (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ℓ ∣ N),
      θbar' (CohCarrier.Gen.U ℓ hℓ hℓM) = θbar (CohCarrier.Gen.U ℓ hℓ hℓN))
    (hθq : θbar' (CohCarrier.Gen.U q hq (dvd_mul_of_dvd_right (dvd_pow_self q two_ne_zero) N)) = 0)
    (hθdia : ∀ d : (ZMod (N * q ^ 2))ˣ, θbar' (CohCarrier.Gen.dia d) = 1)

    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)

    (hinj : ∀ φ : CohCarrier.H1 N ⊤ 𝒪,
      φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
      ((q : 𝒪) • CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
          - (CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          + CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2) φ = 0 → φ = 0) :
    ∃ (Sp' : IharaLemma.IdempotentSplitting
        ↥(CohCarrier.hdata (N * q ^ 2) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').opSubalgebra)
      (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] IsLocalRing.ResidueField 𝒪),
      ∀ g : CohCarrier.Gen (N * q ^ 2) S, πk' (Sp'.toCornerRing i₀'
        ⟨(CohCarrier.hdata (N * q ^ 2) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').op g,
          Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar' g := by

  haveI : Module.Finite 𝒪 (CohCarrier.H1 (N * q ^ 2) ⊤ 𝒪) :=
    CohCarrier.H1_moduleFinite (N * q ^ 2) ⊤ 𝒪 𝒪
  obtain ⟨Sp'⟩ := CohCarrier.HeckeData.nonempty_idempotentSplitting_opSubalgebra
    (CohCarrier.hdata (N * q ^ 2) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar')
  obtain ⟨i₀', πk', hπk'⟩ := OccupancySol.exists_index_algHom N q hq hqN h1 hq' hq2 S 𝒪
    (IsLocalRing.ResidueField 𝒪) hcomm hcomm' θbar θbar' Sp i₀ πk hπk hθT hθU hθq hθdia
    (fun φ hφ h => hinj φ hφ h) IsLocalRing.residue_surjective Sp'
  exact ⟨Sp', i₀', πk', hπk'⟩

end
p2m_reactivate "P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_sq_of_prime.OccupancySol"

end S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_sq_of_prime
end P2MW
export P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_sq_of_prime (solution)
