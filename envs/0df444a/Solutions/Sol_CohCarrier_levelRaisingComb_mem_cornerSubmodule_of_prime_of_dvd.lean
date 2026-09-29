-- Prove2me | solution 1 for CohCarrier.levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/04174ab1-c32d-5bfe-8d29-ccfb4160ba03

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CohCarrier_heckeT_iDeg_one_comm_of_dvd
import Theorems.Thm_CohCarrier_heckeT_iDeg_q_eq_smul
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace LevelRaisingCornerDvdSol

open CohCarrier IharaLemma Polynomial
open scoped IsMulCommutative MatrixGroups
open CongruenceSubgroup

section Abstract

variable {B : Type} [CommRing B] (S : IdempotentSplitting B)

theorem one_sub_e_mem_iff (i j : Fin S.n) : 1 - S.e i ∈ S.𝔪 j ↔ j = i := by
  constructor
  · intro h
    by_contra hji
    have hei : S.e i ∈ S.𝔪 j := S.mem_of_ne (fun h' => hji h'.symm)
    have : (1 : B) ∈ S.𝔪 j := by
      have := (S.𝔪 j).add_mem h hei
      rwa [sub_add_cancel] at this
    exact (S.isMaximal j).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  · rintro rfl
    have hsum : ∑ i, S.e i = 1 := S.coi.complete
    classical
    have : 1 - S.e j = ∑ i ∈ Finset.univ.erase j, S.e i := by
      rw [← hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_sub_cancel_right]
    rw [this]
    refine Ideal.sum_mem _ fun i hi => ?_
    exact S.mem_of_ne (Finset.ne_of_mem_erase hi)

variable {M : Type} [AddCommGroup M] [Module B M]

theorem mem_cornerSubmodule_iff (e : B) (he : IsIdempotentElem e) (v : M) :
    v ∈ cornerSubmodule (M := M) e ↔ e • v = v := by
  constructor
  · rintro ⟨v₀, rfl⟩
    show e • (e • v₀) = e • v₀
    rw [smul_smul, he.eq]
  · intro h
    exact ⟨v, h⟩

theorem mem_corner_iff_forall_smul_eq_zero (i : Fin S.n) (v : M) :
    v ∈ cornerSubmodule (M := M) (S.e i) ↔ ∀ j, j ≠ i → S.e j • v = 0 := by
  rw [mem_cornerSubmodule_iff _ (S.idem i)]
  constructor
  · intro h j hji
    rw [← h, smul_smul, S.coi.ortho hji, zero_smul]
  · intro h
    classical
    have hsum : ∑ j, S.e j = 1 := S.coi.complete
    calc S.e i • v = (∑ j, S.e j) • v - ∑ j ∈ Finset.univ.erase i, S.e j • v := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_smul, Finset.sum_smul,
              add_sub_cancel_left]
      _ = v := by
            rw [hsum, one_smul, Finset.sum_eq_zero (fun j hj => h j (Finset.ne_of_mem_erase hj)),
              sub_zero]

theorem e_smul_eq_zero_of_smul_eq_zero (j : Fin S.n) {s : B} (hs : s ∉ S.𝔪 j) {v : M}
    (hv : s • v = 0) : S.e j • v = 0 := by
  obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem (S.idem j) (S.𝔪 j) (S.mem_of_isMaximal_of_ne j) hs
  rw [← ht, mul_comm t s, mul_assoc, mul_comm s, mul_smul, hv, smul_zero]

variable {F : Type} [CommRing F] {B' : Type} [CommRing B'] (S' : IdempotentSplitting B')
  {M' : Type} [AddCommGroup M'] [Module B' M']

theorem comap_eq_of_span_le (ψ : F →+* B)
    (hψ : ∀ b : B, ∃ p : Polynomial F, p.Monic ∧ Polynomial.eval₂ ψ b p = 0) (i : Fin S.n)
    (P : Ideal F) [hP : P.IsMaximal] (hle : (Ideal.span {1 - S.e i}).comap ψ ≤ P) :
    (S.𝔪 i).comap ψ = P := by
  set I : Ideal B := Ideal.span {1 - S.e i} with hI
  letI : Algebra F (B ⧸ I) := ((Ideal.Quotient.mk I).comp ψ).toAlgebra
  have halg : algebraMap F (B ⧸ I) = (Ideal.Quotient.mk I).comp ψ := rfl
  haveI : Algebra.IsIntegral F (B ⧸ I) := ⟨fun x => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hpb⟩ := hψ b
    refine ⟨p, hp, ?_⟩
    rw [halg, ← Polynomial.hom_eval₂, hpb, map_zero]⟩
  have hker : RingHom.ker (algebraMap F (B ⧸ I)) ≤ P := by
    intro g hg
    apply hle
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    rw [RingHom.mem_ker, halg] at hg
    exact hg
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hker
  set Q' : Ideal B := Q.comap (Ideal.Quotient.mk I) with hQ'
  haveI hQ'max : Q'.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have h1e : 1 - S.e i ∈ Q' := by
    have h0 : (Ideal.Quotient.mk I) (1 - S.e i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hQ', Ideal.mem_comap, h0]
    exact Q.zero_mem
  obtain ⟨j₀, hj₀⟩ := S.exists_eq Q' hQ'max
  have hj₀i : j₀ = i := (one_sub_e_mem_iff S i j₀).mp (hj₀ ▸ h1e)
  subst hj₀i
  rw [hj₀, hQ', Ideal.comap_comap, ← halg, hQ]

theorem map_mem_cornerSubmodule_of_comap_eq (ψ : F →+* B) (ψ' : F →+* B')
    (hψ : ∀ b : B, ∃ p : Polynomial F, p.Monic ∧ Polynomial.eval₂ ψ b p = 0)
    (hψ' : Function.Surjective ψ')
    (i : Fin S.n) (i' : Fin S'.n) (hcomap : (S.𝔪 i).comap ψ = (S'.𝔪 i').comap ψ')
    (w : M →+ M') (hw : ∀ (f : F) (v : M), w (ψ f • v) = ψ' f • w v)
    (v : M) (hv : v ∈ cornerSubmodule (M := M) (S.e i)) :
    w v ∈ cornerSubmodule (M := M') (S'.e i') := by
  rw [mem_corner_iff_forall_smul_eq_zero]
  intro j hj

  have hex : ∃ g : F, ψ g ∈ Ideal.span {1 - S.e i} ∧ ψ' g ∉ S'.𝔪 j := by
    by_contra hne
    push Not at hne
    have hle : (Ideal.span {1 - S.e i}).comap ψ ≤ (S'.𝔪 j).comap ψ' := fun g hg => hne g hg
    haveI hPmax : ((S'.𝔪 j).comap ψ').IsMaximal := Ideal.comap_isMaximal_of_surjective ψ' hψ'
    have hcm : (S'.𝔪 j).comap ψ' = (S'.𝔪 i').comap ψ' := by
      rw [← hcomap, comap_eq_of_span_le S ψ hψ i ((S'.𝔪 j).comap ψ') hle]
    have : S'.𝔪 j = S'.𝔪 i' := by
      rw [← Ideal.map_comap_of_surjective ψ' hψ' (S'.𝔪 j), hcm,
        Ideal.map_comap_of_surjective ψ' hψ']
    exact hj (S'.𝔪_injective this)
  obtain ⟨g, hg, hg'⟩ := hex
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hg
  refine e_smul_eq_zero_of_smul_eq_zero S' j hg' ?_
  rw [← hw, ← hb]
  have hv' : (1 - S.e i) • v = 0 := by
    rw [sub_smul, one_smul, (mem_cornerSubmodule_iff _ (S.idem i) v).mp hv, sub_self]
  rw [mul_smul, hv', smul_zero, map_zero]

end Abstract

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

theorem freeToT_X (g : Gen M S) : freeToT M S 𝒪 k hcomm θbar (MvPolynomial.X g) = gOp M S 𝒪 k hcomm θbar g := by
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

theorem isIntegral_of_algHom [IsNoetherianRing 𝒪] {F : Type} [CommRing F] [Algebra 𝒪 F]
    (ψ : F →ₐ[𝒪] ↥𝕋) :
    ∀ b : ↥𝕋, ∃ p : Polynomial F, p.Monic ∧ Polynomial.eval₂ (ψ : F →+* ↥𝕋) b p = 0 := by
  haveI : Module.Finite 𝒪 (H1 M ⊤ 𝒪) := H1_moduleFinite M ⊤ 𝒪 𝒪
  intro b
  obtain ⟨p, hp, hpb⟩ := LinearMap.exists_monic_and_aeval_eq_zero 𝒪 (b : Module.End 𝒪 (H1 M ⊤ 𝒪))
  have hb : Polynomial.aeval b p = 0 := by
    apply Subtype.ext
    show (Subalgebra.val _) (Polynomial.aeval b p) = 0
    rw [← Polynomial.aeval_algHom_apply]
    exact hpb
  refine ⟨p.map (algebraMap 𝒪 F), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, AlgHom.comp_algebraMap, ← Polynomial.aeval_def, hb]

variable (Sp : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdata M ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n)

noncomputable def toCornerAlg : ↥𝕋 →ₐ[𝒪] Sp.CornerRing i₀ where
  toFun := Sp.toCornerRing i₀
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' _ := rfl

@[scoped simp] theorem toCornerAlg_apply (b : ↥𝕋) : toCornerAlg M S 𝒪 k hcomm θbar Sp i₀ b = Sp.toCornerRing i₀ b := rfl

variable (πk : Sp.CornerRing i₀ →ₐ[𝒪] k)

theorem toCornerRing_one_sub_e : Sp.toCornerRing i₀ (1 - Sp.e i₀) = 0 := by
  apply Subtype.ext
  rw [IdempotentSplitting.coe_toCornerRing]
  show Sp.e i₀ * (1 - Sp.e i₀) * Sp.e i₀ = 0
  linear_combination (-Sp.e i₀) * (Sp.idem i₀).eq

theorem 𝔪_eq_ker (hk : Function.Surjective (algebraMap 𝒪 k)) :
    Sp.𝔪 i₀ = RingHom.ker (πk.comp (toCornerAlg M S 𝒪 k hcomm θbar Sp i₀)) := by
  set χ : ↥𝕋 →ₐ[𝒪] k := πk.comp (toCornerAlg M S 𝒪 k hcomm θbar Sp i₀) with hχ
  have hsurj : Function.Surjective χ := fun x => by
    obtain ⟨r, rfl⟩ := hk x
    exact ⟨algebraMap 𝒪 _ r, χ.commutes r⟩
  haveI hmax : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hsurj
  obtain ⟨j, hj⟩ := Sp.exists_eq _ hmax
  have h1e : (1 : ↥𝕋) - Sp.e i₀ ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker, hχ, AlgHom.comp_apply, toCornerAlg_apply, toCornerRing_one_sub_e, map_zero]
  rw [← hj] at h1e ⊢
  rw [(one_sub_e_mem_iff Sp i₀ j).mp h1e]

theorem gOp_T_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) [NeZero ℓ] (v : H1 M ⊤ 𝒪) :
    (gOp M S 𝒪 k hcomm θbar (Gen.T ℓ hℓ hℓS hℓM)) • v = heckeT M ⊤ ℓ 𝒪 v := rfl

theorem gOp_U_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) [NeZero ℓ] (v : H1 M ⊤ 𝒪) :
    (gOp M S 𝒪 k hcomm θbar (Gen.U ℓ hℓ hℓM)) • v = heckeT M ⊤ ℓ 𝒪 v := rfl

theorem gOp_dia_smul (d : (ZMod M)ˣ) (v : H1 M ⊤ 𝒪) :
    (gOp M S 𝒪 k hcomm θbar (Gen.dia d)) • v = v := by
  rw [gOp_dia_eq_one, one_smul]

theorem algebraMap_smul_eq (r : 𝒪) (v : H1 M ⊤ 𝒪) : (algebraMap 𝒪 ↥𝕋 r) • v = r • v :=
  algebraMap_smul _ r v

theorem comap_𝔪_eq_ker_aeval (hk : Function.Surjective (algebraMap 𝒪 k)) {G : Type}
    (ψ : MvPolynomial G 𝒪 →ₐ[𝒪] ↥𝕋) :
    (Sp.𝔪 i₀).comap ψ =
      RingHom.ker (MvPolynomial.aeval (R := 𝒪)
        (fun g => πk (Sp.toCornerRing i₀ (ψ (MvPolynomial.X g))))) := by
  have hfun : (πk.comp (toCornerAlg M S 𝒪 k hcomm θbar Sp i₀)).comp ψ =
      MvPolynomial.aeval (R := 𝒪) (fun g => πk (Sp.toCornerRing i₀ (ψ (MvPolynomial.X g)))) := by
    apply MvPolynomial.algHom_ext
    intro g
    rw [MvPolynomial.aeval_X, AlgHom.comp_apply, AlgHom.comp_apply, toCornerAlg_apply]
  rw [𝔪_eq_ker M S 𝒪 k hcomm θbar Sp i₀ πk hk, ← hfun]
  ext f
  simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.comp_apply]

end Hecke

section TwoLevels

theorem heckeT_smul (M : ℕ) (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪] (ℓ : ℕ) [NeZero ℓ]
    (r : 𝒪) (x : H1 M H 𝒪) : heckeT M H ℓ 𝒪 (r • x) = r • heckeT M H ℓ 𝒪 x :=
  (heckeTL M H 𝒪 ℓ).map_smul r x

variable (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : q ∣ N)
  (h1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
  (hq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
  (S : Set ℕ) (hqS : q ∈ S) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
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
  (Sp' : IharaLemma.IdempotentSplitting
    ↥(CohCarrier.hdata (N * q) ⊤ S 𝒪 k hcomm' θbar').opSubalgebra)
  (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] k)
  (hπk' : ∀ g : Gen (N * q) S, πk' (Sp'.toCornerRing i₀'
    ⟨(hdata (N * q) ⊤ S 𝒪 k hcomm' θbar').op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) =
      θbar' g)
  (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q),
    θbar' (Gen.T ℓ hℓ hℓS hℓM) = θbar (Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h q))))
  (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q) (hℓN : ℓ ∣ N), ℓ ≠ q →
    θbar' (Gen.U ℓ hℓ hℓM) = θbar (Gen.U ℓ hℓ hℓN))
  (hθq : θbar' (Gen.U q hq (dvd_mul_left q N)) = 0)

include hπk in
theorem hπk_gOp (g : Gen N S) : πk (Sp.toCornerRing i₀ (gOp N S 𝒪 k hcomm θbar g)) = θbar g := hπk g

include hπk' in
theorem hπk'_gOp (g : Gen (N * q) S) :
    πk' (Sp'.toCornerRing i₀' (gOp (N * q) S 𝒪 k hcomm' θbar' g)) = θbar' g := hπk' g

set_option maxHeartbeats 16000000 in
include hq hπk hπk' hθT hθU hθq in

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
    have h' := hπk'_gOp N q S 𝒪 k hcomm' θbar' Sp' i₀' πk' hπk' (Gen.dia d)
    rw [gOp_dia_eq_one (N * q) S 𝒪 k hcomm' θbar' d, RingHom.map_one, map_one] at h'
    rw [τ_dia, RingHom.map_one, map_one, h']

set_option maxHeartbeats 16000000 in
include hq hπk hπk' hθT hθU hθq in

theorem comap_eq (hk : Function.Surjective (algebraMap 𝒪 k)) :
    (Sp.𝔪 i₀).comap (ψ N q S 𝒪 k hcomm θbar).toRingHom =
      (Sp'.𝔪 i₀').comap (freeToT (N * q) S 𝒪 k hcomm' θbar').toRingHom := by
  have H : (Sp.𝔪 i₀).comap (ψ N q S 𝒪 k hcomm θbar) =
      (Sp'.𝔪 i₀').comap (freeToT (N * q) S 𝒪 k hcomm' θbar') := by
    rw [comap_𝔪_eq_ker_aeval N S 𝒪 k hcomm θbar Sp i₀ πk hk,
      comap_𝔪_eq_ker_aeval (N * q) S 𝒪 k hcomm' θbar' Sp' i₀' πk' hk]
    have hfg : (fun g => πk (Sp.toCornerRing i₀ (ψ N q S 𝒪 k hcomm θbar (MvPolynomial.X g)))) =
        (fun g => πk' (Sp'.toCornerRing i₀'
          (freeToT (N * q) S 𝒪 k hcomm' θbar' (MvPolynomial.X g)))) := by
      funext g
      rw [ψ_X, freeToT_X,
        πk_τ_eq N q hq S 𝒪 k hcomm hcomm' θbar θbar' Sp i₀ πk hπk Sp' i₀' πk' hπk' hθT hθU hθq,
        hπk'_gOp N q S 𝒪 k hcomm' θbar' Sp' i₀' πk' hπk']
    rw [hfg]
  ext f
  exact SetLike.ext_iff.mp H f

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

set_option maxHeartbeats 16000000 in
include hq hqN hπk hπk' hθT hθU hθq in

theorem wL_mem_cornerSubmodule [IsNoetherianRing 𝒪] (hk : Function.Surjective (algebraMap 𝒪 k))
    (φ : H1 N ⊤ 𝒪) (hφ : φ ∈ IharaLemma.cornerSubmodule (M := H1 N ⊤ 𝒪) (Sp.e i₀)) :
    wL N q h1 hq' 𝒪 φ ∈ IharaLemma.cornerSubmodule (M := H1 (N * q) ⊤ 𝒪) (Sp'.e i₀') :=
  map_mem_cornerSubmodule_of_comap_eq Sp Sp' (ψ N q S 𝒪 k hcomm θbar).toRingHom
    (freeToT (N * q) S 𝒪 k hcomm' θbar').toRingHom
    (isIntegral_of_algHom N S 𝒪 k hcomm θbar (ψ N q S 𝒪 k hcomm θbar))
    (freeToT_surjective (N * q) S 𝒪 k hcomm' θbar')
    i₀ i₀' (comap_eq N q hq S 𝒪 k hcomm hcomm' θbar θbar' Sp i₀ πk hπk Sp' i₀' πk' hπk' hθT hθU hθq hk)
    (wL N q h1 hq' 𝒪).toAddMonoidHom
    (fun f v => wL_ψ_smul N q hq hqN h1 hq' S 𝒪 k hcomm hcomm' θbar θbar' f v) φ hφ

end TwoLevels

end LevelRaisingCornerDvdSol
p2m_reactivate "P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd.LevelRaisingCornerDvdSol"

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

    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (Sp' : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata (N * q) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').opSubalgebra)
    (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk' : ∀ g : CohCarrier.Gen (N * q) S, πk' (Sp'.toCornerRing i₀'
      ⟨(CohCarrier.hdata (N * q) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar' g)
    (φ : CohCarrier.H1 N ⊤ 𝒪)
    (hφ : φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)) :
    ((CohCarrier.iDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
        - (q : 𝒪) • CohCarrier.iDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1) φ ∈
      IharaLemma.cornerSubmodule (M := CohCarrier.H1 (N * q) ⊤ 𝒪) (Sp'.e i₀') :=
  LevelRaisingCornerDvdSol.wL_mem_cornerSubmodule N q hq hqN h1 hq' S 𝒪
    (IsLocalRing.ResidueField 𝒪) hcomm hcomm' θbar θbar' Sp i₀ πk hπk Sp' i₀' πk' hπk' hθT hθU hθq
    IsLocalRing.residue_surjective φ hφ

end
p2m_reactivate "P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd.LevelRaisingCornerDvdSol"

end S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd
end P2MW
export P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd (solution)
