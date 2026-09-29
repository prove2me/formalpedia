-- Prove2me | solution 1 for CohCarrier.exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6c7eade2-313a-593b-b043-7fe31b1d4435

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CohCarrier_heckeT_iDeg_one_comm_of_dvd
import Theorems.Thm_CohCarrier_heckeT_iDeg_q_eq_smul
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace OccupancyDvdSol

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

section TwoLevels

theorem heckeT_smul (M : ℕ) (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪] (ℓ : ℕ) [NeZero ℓ]
    (r : 𝒪) (x : H1 M H 𝒪) : heckeT M H ℓ 𝒪 (r • x) = r • heckeT M H ℓ 𝒪 x :=
  (heckeTL M H 𝒪 ℓ).map_smul r x

variable (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : q ∣ N)
  (h1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
  (hq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
  (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  (hcomm : ∀ g g' : Gen N S,
      opFamily N ⊤ S 𝒪 g * opFamily N ⊤ S 𝒪 g' = opFamily N ⊤ S 𝒪 g' * opFamily N ⊤ S 𝒪 g)
  (hcomm' : ∀ g g' : Gen (N * q) S,
      opFamily (N * q) ⊤ S 𝒪 g * opFamily (N * q) ⊤ S 𝒪 g' =
        opFamily (N * q) ⊤ S 𝒪 g' * opFamily (N * q) ⊤ S 𝒪 g)
  (θbar : Gen N S → k) (θbar' : Gen (N * q) S → k)

local notation3 "𝕋" => (CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra
local notation3 "𝕋'" => (CohCarrier.hdata (N * q) ⊤ S 𝒪 k hcomm' θbar').opSubalgebra

include hq in

theorem dvd_of_dvd_mul_of_ne {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q) (hℓq : ℓ ≠ q) : ℓ ∣ N := by
  rcases (Nat.Prime.dvd_mul hℓ).mp hℓM with h | h
  · exact h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp h) hℓq

noncomputable def τ : Gen (N * q) S → ↥𝕋
  | .T ℓ hℓ hℓS hℓM => gOp N S 𝒪 k hcomm θbar (.T ℓ hℓ hℓS (fun h => hℓM (h.mul_right _)))
  | .U ℓ hℓ _ => if h : ℓ ≠ q ∧ ℓ ∣ N then gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ h.2) else 0
  | .dia _ => 1

theorem τ_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q) (hℓN : ¬ ℓ ∣ N) :
    τ N q S 𝒪 k hcomm θbar (.T ℓ hℓ hℓS hℓM) = gOp N S 𝒪 k hcomm θbar (.T ℓ hℓ hℓS hℓN) := rfl

theorem τ_U_of_ne (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q) (hℓq : ℓ ≠ q) (hℓN : ℓ ∣ N) :
    τ N q S 𝒪 k hcomm θbar (.U ℓ hℓ hℓM) = gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ hℓN) := by
  show (if h : ℓ ≠ q ∧ ℓ ∣ N then gOp N S 𝒪 k hcomm θbar (.U ℓ hℓ h.2) else 0) = _
  rw [dif_pos ⟨hℓq, hℓN⟩]

theorem τ_U_self (hqM : q ∣ N * q) :
    τ N q S 𝒪 k hcomm θbar (.U q hq hqM) = 0 := by
  show (if h : q ≠ q ∧ q ∣ N then gOp N S 𝒪 k hcomm θbar (.U q hq h.2) else 0) = _
  rw [dif_neg (fun h => h.1 rfl)]

theorem τ_dia (d : (ZMod (N * q))ˣ) : τ N q S 𝒪 k hcomm θbar (.dia d) = 1 := rfl

noncomputable def ψ : MvPolynomial (Gen (N * q) S) 𝒪 →ₐ[𝒪] ↥𝕋 :=
  MvPolynomial.aeval (τ N q S 𝒪 k hcomm θbar)

theorem ψ_X (g : Gen (N * q) S) :
    ψ N q S 𝒪 k hcomm θbar (MvPolynomial.X g) = τ N q S 𝒪 k hcomm θbar g := by
  simp [ψ]

theorem ψ_C (r : 𝒪) : ψ N q S 𝒪 k hcomm θbar (MvPolynomial.C r) = algebraMap 𝒪 ↥𝕋 r :=
  MvPolynomial.aeval_C _ r

variable (Sp : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] k)
  (hπk : ∀ g : Gen N S, πk (Sp.toCornerRing i₀
    ⟨(hdata N ⊤ S 𝒪 k hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
  (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q),
    θbar' (Gen.T ℓ hℓ hℓS hℓM) = θbar (Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h q))))
  (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q) (hℓN : ℓ ∣ N), ℓ ≠ q →
    θbar' (Gen.U ℓ hℓ hℓM) = θbar (Gen.U ℓ hℓ hℓN))
  (hθq : θbar' (Gen.U q hq (dvd_mul_left q N)) = 0)
  (hθdia : ∀ d : (ZMod (N * q))ˣ, θbar' (Gen.dia d) = 1)

include hπk in
theorem hπk_gOp (g : Gen N S) : πk (Sp.toCornerRing i₀ (gOp N S 𝒪 k hcomm θbar g)) = θbar g := hπk g

set_option maxHeartbeats 16000000 in
include hq hπk hθT hθU hθq hθdia in

theorem πk_τ_eq (g : Gen (N * q) S) :
    πk (Sp.toCornerRing i₀ (τ N q S 𝒪 k hcomm θbar g)) = θbar' g := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    rw [τ_T N q S 𝒪 k hcomm θbar ℓ hℓ hℓS hℓM (fun h => hℓM (Dvd.dvd.mul_right h q)),
      hπk_gOp N S 𝒪 k hcomm θbar Sp i₀ πk hπk, hθT]
  | U ℓ hℓ hℓM =>
    by_cases h : ℓ = q
    · subst h
      have hz : ∀ (hℓM' : ℓ ∣ N * ℓ), θbar' (Gen.U ℓ hℓ hℓM') = 0 := fun _ => hθq
      rw [τ_U_self, RingHom.map_zero, map_zero, hz]
    · rw [τ_U_of_ne N q S 𝒪 k hcomm θbar ℓ hℓ hℓM h (dvd_of_dvd_mul_of_ne N q hq hℓ hℓM h),
        hπk_gOp N S 𝒪 k hcomm θbar Sp i₀ πk hπk, hθU ℓ hℓ hℓM _ h]
  | dia d =>
    rw [τ_dia, RingHom.map_one, map_one, hθdia]

noncomputable def wL : H1 N ⊤ 𝒪 →ₗ[𝒪] H1 (N * q) ⊤ 𝒪 :=
  (iDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq').comp (heckeTL N ⊤ 𝒪 q)
    - (q : 𝒪) • iDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1

theorem wL_apply (v : H1 N ⊤ 𝒪) :
    wL N q h1 hq' 𝒪 v = iDeg' N (N * q) ⊤ ⊤ q 𝒪 hq' (heckeT N ⊤ q 𝒪 v)
      - (q : 𝒪) • iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h1 v := rfl

include hqN in

theorem heckeT_wL_eq_zero (v : H1 N ⊤ 𝒪) : heckeT (N * q) ⊤ q 𝒪 (wL N q h1 hq' 𝒪 v) = 0 := by
  rw [wL_apply, map_sub, heckeT_iDeg_q_eq_smul h1 hq' (heckeT N ⊤ q 𝒪 v), heckeT_smul,
    heckeT_iDeg_one_comm_of_dvd h1 hqN v, Nat.cast_smul_eq_nsmul, sub_self]

include hq hqN in

theorem wL_τ_smul (g : Gen (N * q) S) (v : H1 N ⊤ 𝒪) :
    wL N q h1 hq' 𝒪 ((τ N q S 𝒪 k hcomm θbar g) • v) =
      (gOp (N * q) S 𝒪 k hcomm' θbar' g) • wL N q h1 hq' 𝒪 v := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓq : ℓ ≠ q := fun h => hℓM (h ▸ dvd_mul_left q N)
    have hcop : Nat.Coprime ℓ q := (Nat.coprime_primes hℓ hq).mpr hℓq
    show wL N q h1 hq' 𝒪 (heckeT N ⊤ ℓ 𝒪 v) = heckeT (N * q) ⊤ ℓ 𝒪 (wL N q h1 hq' 𝒪 v)
    rw [wL_apply, wL_apply, map_sub, heckeT_smul,
      heckeT_comm_of_prime N ⊤ q ℓ hq hcop.symm v,
      iDeg_heckeT_comm_of_coprime h1 (Nat.coprime_one_right ℓ) hℓ hℓM,
      iDeg_heckeT_comm_of_coprime hq' hcop hℓ hℓM]
  | U ℓ hℓ hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    by_cases h : ℓ = q
    · subst h
      rw [τ_U_self, zero_smul, map_zero]
      show 0 = heckeT (N * ℓ) ⊤ ℓ 𝒪 (wL N ℓ h1 hq' 𝒪 v)
      rw [heckeT_wL_eq_zero N ℓ hqN]
    · have hℓN : ℓ ∣ N := dvd_of_dvd_mul_of_ne N q hq hℓ hℓM h
      have hcop : Nat.Coprime ℓ q := (Nat.coprime_primes hℓ hq).mpr h
      rw [τ_U_of_ne N q S 𝒪 k hcomm θbar ℓ hℓ hℓM h hℓN]
      show wL N q h1 hq' 𝒪 (heckeT N ⊤ ℓ 𝒪 v) = heckeT (N * q) ⊤ ℓ 𝒪 (wL N q h1 hq' 𝒪 v)
      rw [wL_apply, wL_apply, map_sub, heckeT_smul,
        heckeT_comm_of_prime N ⊤ q ℓ hq hcop.symm v,
        iDeg_heckeT_comm_of_dvd h1 (Nat.coprime_one_right ℓ) hℓN,
        iDeg_heckeT_comm_of_dvd hq' hcop hℓN]
  | dia d =>
    rw [gOp_dia_smul]
    show wL N q h1 hq' 𝒪 ((1 : ↥𝕋) • v) = _
    rw [one_smul]

set_option maxHeartbeats 16000000 in
include hq hqN in

theorem wL_ψ_smul (f : MvPolynomial (Gen (N * q) S) 𝒪) (v : H1 N ⊤ 𝒪) :
    wL N q h1 hq' 𝒪 ((ψ N q S 𝒪 k hcomm θbar f) • v) =
      (freeToT (N * q) S 𝒪 k hcomm' θbar' f) • wL N q h1 hq' 𝒪 v := by
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
    wL N q h1 hq' 𝒪 φ = 0 → φ = 0)

noncomputable def χ : MvPolynomial (Gen (N * q) S) 𝒪 →ₐ[𝒪] k :=
  (πk.comp (toCornerAlg N S 𝒪 k hcomm θbar Sp i₀)).comp (ψ N q S 𝒪 k hcomm θbar)

theorem χ_apply (f : MvPolynomial (Gen (N * q) S) 𝒪) :
    χ N q S 𝒪 k hcomm θbar Sp i₀ πk f = πk (Sp.toCornerRing i₀ (ψ N q S 𝒪 k hcomm θbar f)) := rfl

include hq hπk hθT hθU hθq hθdia in
theorem χ_X (g : Gen (N * q) S) :
    χ N q S 𝒪 k hcomm θbar Sp i₀ πk (MvPolynomial.X g) = θbar' g := by
  rw [χ_apply, ψ_X]
  exact πk_τ_eq N q hq S 𝒪 k hcomm θbar θbar' Sp i₀ πk hπk hθT hθU hθq hθdia g

set_option maxHeartbeats 16000000 in
include hq hqN hinj in

theorem χ_eq_zero_of_freeToT_eq_zero (f : MvPolynomial (Gen (N * q) S) 𝒪)
    (hf : freeToT (N * q) S 𝒪 k hcomm' θbar' f = 0) :
    χ N q S 𝒪 k hcomm θbar Sp i₀ πk f = 0 := by
  rw [χ_apply]
  have hkill : ∀ v : H1 N ⊤ 𝒪, v ∈ IharaLemma.cornerSubmodule (M := H1 N ⊤ 𝒪) (Sp.e i₀) →
      (ψ N q S 𝒪 k hcomm θbar f) • v = 0 := by
    intro v hv
    refine hinj _ (Submodule.smul_mem _ _ hv) ?_
    rw [wL_ψ_smul N q hq hqN h1 hq' S 𝒪 k hcomm hcomm' θbar θbar' f v, hf, zero_smul]
  rw [toCornerRing_eq_zero_of_forall_smul_eq_zero N S 𝒪 k hcomm θbar Sp i₀ _ hkill, map_zero]

include hq hqN hπk hθT hθU hθq hθdia hinj in

theorem exists_residualPoint :
    ∃ ρ : ↥𝕋' →ₐ[𝒪] k,
      ∀ g : Gen (N * q) S, ρ (gOp (N * q) S 𝒪 k hcomm' θbar' g) = θbar' g := by
  obtain ⟨ρ, hρ⟩ := exists_algHom_comp_eq_of_surjective (freeToT (N * q) S 𝒪 k hcomm' θbar')
    (freeToT_surjective (N * q) S 𝒪 k hcomm' θbar') (χ N q S 𝒪 k hcomm θbar Sp i₀ πk)
    (χ_eq_zero_of_freeToT_eq_zero N q hq hqN h1 hq' S 𝒪 k hcomm hcomm' θbar θbar' Sp i₀ πk hinj)
  refine ⟨ρ, fun g => ?_⟩
  rw [← freeToT_X, hρ]
  exact χ_X N q hq S 𝒪 k hcomm θbar θbar' Sp i₀ πk hπk hθT hθU hθq hθdia g

include hq hqN hπk hθT hθU hθq hθdia hinj in

theorem exists_index_algHom (hk : Function.Surjective (algebraMap 𝒪 k))
    (Sp' : IharaLemma.IdempotentSplitting ↥𝕋') :
    ∃ (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] k),
      ∀ g : Gen (N * q) S,
        πk' (Sp'.toCornerRing i₀' (gOp (N * q) S 𝒪 k hcomm' θbar' g)) = θbar' g := by
  obtain ⟨ρ, hρ⟩ := exists_residualPoint N q hq hqN h1 hq' S 𝒪 k hcomm hcomm' θbar θbar' Sp i₀
    πk hπk hθT hθU hθq hθdia hinj
  have hsurj : Function.Surjective ρ := fun x => by
    obtain ⟨r, rfl⟩ := hk x
    exact ⟨algebraMap 𝒪 _ r, AlgHom.commutes ρ r⟩
  haveI hmax : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective ρ hsurj
  obtain ⟨i₀', hi₀'⟩ := Sp'.exists_eq _ hmax
  obtain ⟨πk', hπk'⟩ := exists_algHom_cornerRing_of_ker_eq Sp' i₀' 𝒪 ρ hi₀'.symm
  exact ⟨i₀', πk', fun g => by rw [hπk', hρ]⟩

end TwoLevels

end OccupancyDvdSol
p2m_reactivate "P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd.OccupancyDvdSol"

set_option maxHeartbeats 16000000 in
open scoped IsMulCommutative in
theorem solution
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : q ∣ N)
    (h1 : CohCarrier.LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq' : CohCarrier.LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (hcomm : ∀ g g' : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 g' =
        CohCarrier.opFamily N ⊤ S 𝒪 g' * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (hcomm' : ∀ g g' : CohCarrier.Gen (N * q) S,
      CohCarrier.opFamily (N * q) ⊤ S 𝒪 g * CohCarrier.opFamily (N * q) ⊤ S 𝒪 g' =
        CohCarrier.opFamily (N * q) ⊤ S 𝒪 g' * CohCarrier.opFamily (N * q) ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → IsLocalRing.ResidueField 𝒪)
    (θbar' : CohCarrier.Gen (N * q) S → IsLocalRing.ResidueField 𝒪)

    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q),
      θbar' (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) =
        θbar (CohCarrier.Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h q))))
    (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q) (hℓN : ℓ ∣ N), ℓ ≠ q →
      θbar' (CohCarrier.Gen.U ℓ hℓ hℓM) = θbar (CohCarrier.Gen.U ℓ hℓ hℓN))
    (hθq : θbar' (CohCarrier.Gen.U q hq (dvd_mul_left q N)) = 0)
    (hθdia : ∀ d : (ZMod (N * q))ˣ, θbar' (CohCarrier.Gen.dia d) = 1)

    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)

    (hinj : ∀ φ : CohCarrier.H1 N ⊤ 𝒪,
      φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
      ((CohCarrier.iDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          - (q : 𝒪) • CohCarrier.iDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1) φ = 0 → φ = 0) :
    ∃ (Sp' : IharaLemma.IdempotentSplitting
        ↥(CohCarrier.hdata (N * q) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').opSubalgebra)
      (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] IsLocalRing.ResidueField 𝒪),
      ∀ g : CohCarrier.Gen (N * q) S, πk' (Sp'.toCornerRing i₀'
        ⟨(CohCarrier.hdata (N * q) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').op g,
          Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar' g := by

  haveI : Module.Finite 𝒪 (CohCarrier.H1 (N * q) ⊤ 𝒪) :=
    CohCarrier.H1_moduleFinite (N * q) ⊤ 𝒪 𝒪
  obtain ⟨Sp'⟩ := CohCarrier.HeckeData.nonempty_idempotentSplitting_opSubalgebra
    (CohCarrier.hdata (N * q) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar')
  obtain ⟨i₀', πk', hπk'⟩ := OccupancyDvdSol.exists_index_algHom N q hq hqN h1 hq' S 𝒪
    (IsLocalRing.ResidueField 𝒪) hcomm hcomm' θbar θbar' Sp i₀ πk hπk hθT hθU hθq hθdia
    (fun φ hφ h => hinj φ hφ h) IsLocalRing.residue_surjective Sp'
  exact ⟨Sp', i₀', πk', hπk'⟩

end
p2m_reactivate "P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd.OccupancyDvdSol"

end S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd
end P2MW
export P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd (solution)
