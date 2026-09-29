-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bfeb5e86-9477-50d5-ac3b-fe41687bc50e

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_WittVector_ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent
import Theorems.Thm_Module_Invertible_of_invertible_baseChange_of_surjective_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace X2R

open Matrix MvFormalGroup TensorProduct

theorem frobenius_teichmuller {p : ℕ} [Fact p.Prime] {k : Type*} [CommRing k] [CharP k p] (c : k) :
    WittVector.frobenius (WittVector.teichmuller p c) = WittVector.teichmuller p (c ^ p) := by
  ext n
  rw [WittVector.coeff_frobenius_charP]
  cases n with
  | zero => rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  | succ n =>
    rw [WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n),
      WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n), zero_pow (Fact.out : p.Prime).ne_zero]

theorem exists_pow_ne (p : ℕ) [hp : Fact p.Prime] : ∃ ζ : GaloisField p 2, ζ ^ p ≠ ζ := by
  by_contra hall
  push Not at hall
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 2 two_ne_zero]
  have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).natDegree = p := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
    exact hp.out.one_lt
  have hf0 : (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    exact hp.out.ne_zero hdeg.symm
  have hsub : (Finset.univ : Finset (GaloisField p 2)).val ⊆
      (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).roots := by
    intro x _
    rw [Polynomial.mem_roots hf0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hall x, sub_self]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_univ, hcard, hdeg, pow_two] at hle
  have h1 := hp.out.one_lt
  nlinarith

theorem mulVec_eq_smul_of_teichmuller {p : ℕ} [Fact p.Prime] {k : Type*} [CommRing k] [CharP k p]
    [PerfectRing k p] {B : Type*} [CommRing B] {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : WittVector p k →+* Matrix n n B) (χ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (v : n → B)
    (h : ∀ c : k, ρ (WittVector.teichmuller p c) *ᵥ v = χ (WittVector.teichmuller p c) • v)
    (a : WittVector p k) : ρ a *ᵥ v = χ a • v := by
  let S : Subring (WittVector p k) :=
    { carrier := {a | ρ a *ᵥ v = χ a • v}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul, ha, smul_smul,
          mul_comm]
      one_mem' := by simp only [Set.mem_setOf_eq, map_one, Matrix.one_mulVec, one_smul]
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, map_add, Matrix.add_mulVec, ha, hb, add_smul]
      zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, Matrix.zero_mulVec, zero_smul]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_neg, map_neg, Matrix.neg_mulVec, ha, neg_smul] }
  obtain ⟨N, hN⟩ := hB
  have hpB : (p : B) ^ (N + 1) = 0 := by rw [pow_succ, hN, zero_mul]
  have hpS : (p : WittVector p k) ∈ S := natCast_mem S p
  have hrest : ∀ c : WittVector p k, (p : WittVector p k) ^ (N + 1) * c ∈ S := by
    intro c
    show ρ _ *ᵥ v = χ _ • v
    rw [map_mul, map_pow, map_natCast, ← Matrix.mulVec_mulVec, ← Nat.cast_pow, Matrix.natCast_mulVec,
      Nat.cast_pow, hpB, zero_smul, map_mul, map_pow, map_natCast, hpB, zero_mul, zero_smul]
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff a N
  rw [sub_eq_iff_eq_add] at hc
  change a ∈ S
  rw [hc]
  exact S.add_mem (hrest c)
    (S.sum_mem fun i _ => S.mul_mem (h _) (S.pow_mem hpS i))

private theorem _root_.X2R.exists_generator (p : ℕ) [hp : Fact p.Prime] :
    ∃ ζ : GaloisField p 2, ζ ^ p ≠ ζ ∧ ∀ c : GaloisField p 2, c = 0 ∨ ∃ n : ℕ, c = ζ ^ n := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  have hpow : ∀ c : GaloisField p 2, c = 0 ∨ ∃ n : ℕ, c = (g : GaloisField p 2) ^ n := by
    intro c
    rcases eq_or_ne c 0 with h | h
    · exact Or.inl h
    · right
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 c h)))
      exact ⟨n, by rw [← Units.val_mk0 h, ← hn, Units.val_pow_eq_pow_val]⟩
  refine ⟨g, fun h => ?_, hpow⟩
  obtain ⟨x, hx⟩ := exists_pow_ne p
  apply hx
  rcases hpow x with h0 | ⟨n, rfl⟩
  · rw [h0, zero_pow hp.out.ne_zero]
  · rw [← pow_mul, mul_comm, pow_mul, h]

p2m_export "X2R" "exists_generator"
variable {p : ℕ} [Fact p.Prime]

local notation "τ" => WittVector.teichmuller p

theorem lie_eq_ker {B : Type} [CommRing B] (hB : IsNilpotent (p : B)) (j : Zp2 p →+* B) (X : FormalODModule p B)
    (ρ : Zp2 p →+* Matrix (Fin 2) (Fin 2) B) (hρ : ∀ a, ρ a = linearPart (X.act a))
    (ζ : GaloisField p 2) (hgen : ∀ c : GaloisField p 2, c = 0 ∨ ∃ n : ℕ, c = ζ ^ n)
    (ui : B) (hui : ui * (j (τ ζ) - j (τ (ζ ^ p))) = 1) :
    X.lieZero j = LinearMap.ker (Matrix.mulVecLin
        (ui • (j (τ ζ) • (1 : Matrix (Fin 2) (Fin 2) B) - ρ (τ ζ)))) ∧
    X.lieOne j = LinearMap.ker (Matrix.mulVecLin
        (ui • (ρ (τ ζ) - j (τ (ζ ^ p)) • (1 : Matrix (Fin 2) (Fin 2) B)))) := by
  classical
  have hlie : ∀ a v, X.lieAct a v = ρ a *ᵥ v := fun a v => by rw [hρ]; rfl
  have mem0 : ∀ v, v ∈ X.lieZero j ↔ ∀ a, ρ a *ᵥ v = j a • v := fun v => by
    rw [FormalODModule.lieZero, Submodule.mem_iInf]
    refine forall_congr' fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, hlie]
  have mem1 : ∀ v, v ∈ X.lieOne j ↔ ∀ a, ρ a *ᵥ v = j (WittVector.frobenius a) • v := fun v => by
    rw [FormalODModule.lieOne, Submodule.mem_iInf]
    refine forall_congr' fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, hlie]
  have cancel : ∀ w : Fin 2 → B, ui • w = 0 ↔ w = 0 := fun w =>
    ⟨fun h => by
      have h2 := congrArg ((j (τ ζ) - j (τ (ζ ^ p))) • ·) h
      simp only [smul_smul, smul_zero] at h2
      rwa [mul_comm, hui, one_smul] at h2,
     fun h => by rw [h, smul_zero]⟩
  have powT : ∀ (v : Fin 2 → B) (x : B), ρ (τ ζ) *ᵥ v = x • v →
      ∀ n : ℕ, ρ (τ ζ ^ n) *ᵥ v = x ^ n • v := by
    intro v x h n
    induction n with
    | zero => rw [pow_zero, pow_zero, map_one, Matrix.one_mulVec, one_smul]
    | succ n ih =>
      rw [pow_succ, map_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have allT : ∀ (v : Fin 2 → B) (χ : Zp2 p →+* B), ρ (τ ζ) *ᵥ v = χ (τ ζ) • v →
      ∀ c, ρ (τ c) *ᵥ v = χ (τ c) • v := by
    intro v χ h c
    rcases hgen c with rfl | ⟨n, rfl⟩
    · rw [WittVector.teichmuller_zero, map_zero, map_zero, Matrix.zero_mulVec, zero_smul]
    · rw [map_pow, powT v _ h n, map_pow]
  constructor
  · ext v
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.smul_mulVec, cancel, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, mem0]
    constructor
    · intro h; exact (h _).symm
    · intro h
      exact mulVec_eq_smul_of_teichmuller ρ j hB v (allT v j h.symm)
  · ext v
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.smul_mulVec, cancel, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, mem1]
    constructor
    · intro h; rw [h, frobenius_teichmuller]
    · intro h a
      have h' : ρ (τ ζ) *ᵥ v = (j.comp WittVector.frobenius) (τ ζ) • v := by
        rw [RingHom.comp_apply, frobenius_teichmuller]; exact h
      have := mulVec_eq_smul_of_teichmuller ρ (j.comp WittVector.frobenius) hB v (allT v _ h') a
      exact this

theorem linearPart_map_act {B B' : Type} [CommRing B] [CommRing B'] (π : B →+* B')
    (X : FormalODModule p B) (a : Zp2 p) :
    linearPart ((X.map π).act a) = (linearPart (X.act a)).map π := by
  ext i k
  simp only [FormalODModule.map_act, linearPart, Matrix.of_apply, Matrix.map_apply]
  exact MvPowerSeries.coeff_map _ _ _

theorem invertible_ker {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (hπ : Function.Surjective (algebraMap R S)) (hker : IsNilpotent (RingHom.ker (algebraMap R S)))
    (e₀ e₁ : Matrix (Fin 2) (Fin 2) R) (hsum : e₀ + e₁ = 1) (h10 : e₁ * e₀ = 0)
    (hinv : Module.Invertible S ↥(LinearMap.ker (Matrix.mulVecLin (e₁.map (algebraMap R S))))) :
    Module.Invertible R ↥(LinearMap.ker (Matrix.mulVecLin e₁)) := by
  classical
  set L := LinearMap.ker (Matrix.mulVecLin e₁) with hL
  set Lb := LinearMap.ker (Matrix.mulVecLin (e₁.map (algebraMap R S))) with hLb
  have he0 : ∀ v : Fin 2 → R, Matrix.mulVecLin e₀ v ∈ L := fun v => by
    rw [hL, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h10,
      Matrix.zero_mulVec]
  have hid : ∀ v ∈ L, e₀ *ᵥ v = v := fun v hv => by
    rw [hL, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
    have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M *ᵥ v) hsum
    simp only [Matrix.add_mulVec, hv, add_zero, Matrix.one_mulVec] at h1
    exact h1
  let s : (Fin 2 → R) →ₗ[R] L := LinearMap.codRestrict L (Matrix.mulVecLin e₀) he0
  have hsi : s ∘ₗ L.subtype = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨v, hv⟩
    apply Subtype.ext
    show e₀ *ᵥ v = v
    exact hid v hv
  haveI : Module.Projective R L := Module.Projective.of_split L.subtype s hsi
  haveI : Module.Finite R L := Module.Finite.of_surjective s fun x => ⟨L.subtype x, LinearMap.congr_fun hsi x⟩

  let φ := TensorProduct.piScalarRight R S S (Fin 2)
  let Θ : S ⊗[R] L →ₗ[S] (Fin 2 → S) := φ.toLinearMap ∘ₗ (L.subtype.baseChange S)
  let Λ : (Fin 2 → S) →ₗ[S] S ⊗[R] L := (s.baseChange S) ∘ₗ φ.symm.toLinearMap
  have hΛΘ : ∀ x, Λ (Θ x) = x := fun x => by
    show (s.baseChange S) (φ.symm (φ ((L.subtype.baseChange S) x))) = x
    rw [LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hsi,
      LinearMap.baseChange_id, LinearMap.id_apply]
  have hΘinj : Function.Injective Θ := Function.LeftInverse.injective hΛΘ
  have hΘtmul : ∀ (t : S) (v : L), Θ (t ⊗ₜ v) = fun i => (v.1 i) • t := fun t v => by
    show φ ((L.subtype.baseChange S) (t ⊗ₜ v)) = _
    rw [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    rfl
  have hmap : ∀ (M : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R),
      (M.map (algebraMap R S)) *ᵥ (algebraMap R S ∘ v) = algebraMap R S ∘ (M *ᵥ v) := fun M v => by
    ext i; exact (RingHom.map_mulVec _ M v i).symm
  have hsmulvec : ∀ (t : S) (v : Fin 2 → R), (fun i => (v i) • t) = t • (algebraMap R S ∘ v) := fun t v => by
    ext i; rw [Pi.smul_apply, Function.comp_apply, smul_eq_mul, Algebra.smul_def, mul_comm]
  have hΘmem : ∀ x, Θ x ∈ Lb := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul t v =>
      rw [hΘtmul, hLb, LinearMap.mem_ker, Matrix.mulVecLin_apply, hsmulvec, Matrix.mulVec_smul, hmap]
      have hv : e₁ *ᵥ v.1 = 0 := LinearMap.mem_ker.mp v.2
      rw [hv]
      ext i; simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  have hsum' : e₀.map (algebraMap R S) + e₁.map (algebraMap R S) = 1 := by
    rw [← Matrix.map_add _ (map_add _), hsum, Matrix.map_one _ (map_zero _) (map_one _)]
  have hΘsurj : ∀ w ∈ Lb, ∃ x, Θ x = w := by
    intro w hw
    have hw0 : (e₀.map (algebraMap R S)) *ᵥ w = w := by
      rw [hLb, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
      have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) S => M *ᵥ w) hsum'
      simp only [Matrix.add_mulVec, hw, add_zero, Matrix.one_mulVec] at h1
      exact h1
    refine ⟨∑ k : Fin 2, w k ⊗ₜ (⟨e₀ *ᵥ Pi.single k 1, he0 _⟩ : L), ?_⟩
    rw [map_sum]
    simp only [hΘtmul, Matrix.mulVec_single_one, Matrix.col_apply]
    conv_rhs => rw [← hw0]
    ext i
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, Fin.sum_univ_two, mul_comm]
  let Θ' : S ⊗[R] L →ₗ[S] Lb := LinearMap.codRestrict Lb Θ hΘmem
  have hbij : Function.Bijective Θ' := by
    refine ⟨fun x y h => hΘinj (congrArg Subtype.val h : (Θ' x).1 = (Θ' y).1), fun w => ?_⟩
    obtain ⟨x, hx⟩ := hΘsurj w.1 w.2
    exact ⟨x, Subtype.ext hx⟩
  let Θe : S ⊗[R] L ≃ₗ[S] Lb := LinearEquiv.ofBijective Θ' hbij
  haveI : Module.Invertible S ↥Lb := hinv
  haveI : Module.Invertible S (S ⊗[R] ↥L) := Module.Invertible.congr Θe.symm
  exact Module.Invertible.of_invertible_baseChange_of_surjective_of_isNilpotent_ker hπ hker L this

end X2R

open Matrix MvFormalGroup

theorem solution
    (p : ℕ) [Fact p.Prime] {R S : Type} [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π)) (hp : IsNilpotent (p : R))
    (j : Zp2 p →+* R) (X : FormalODModule p R) (h : (X.map π).IsSpecial (π.comp j)) :
    X.IsSpecial j := by
  classical
  letI : Algebra R S := π.toAlgebra
  have hπ' : Function.Surjective (algebraMap R S) := hπ
  have hker' : IsNilpotent (RingHom.ker (algebraMap R S)) := hker
  have hpS : IsNilpotent (p : S) := by
    obtain ⟨N, hN⟩ := hp
    exact ⟨N, by rw [← map_natCast π, ← map_pow, hN, map_zero]⟩
  obtain ⟨ζ, hζp, hgen⟩ := X2R.exists_generator p
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Zp2 p →+* Matrix (Fin 2) (Fin 2) R, ∀ a, ρ a = MvFormalGroup.linearPart (X.act a) :=
    ⟨(MvFormalGroup.linearPartHom X.F).comp X.actRingHom, fun _ => rfl⟩
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : Zp2 p →+* Matrix (Fin 2) (Fin 2) S,
      ∀ a, ρ' a = MvFormalGroup.linearPart ((X.map π).act a) :=
    ⟨(MvFormalGroup.linearPartHom (X.map π).F).comp (X.map π).actRingHom, fun _ => rfl⟩
  have hρmap : ∀ a, ρ' a = (ρ a).map π := fun a => by rw [hρ', hρ, X2R.linearPart_map_act]

  obtain ⟨T, hT⟩ : ∃ T : Zp2 p, T = WittVector.teichmuller p ζ := ⟨_, rfl⟩
  have hTp : WittVector.teichmuller p (ζ ^ p) = WittVector.frobenius T := by
    rw [hT, X2R.frobenius_teichmuller]
  obtain ⟨α, hα⟩ : ∃ α : R, α = j T := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : R, β = j (WittVector.teichmuller p (ζ ^ p)) := ⟨_, rfl⟩
  have hd : IsUnit (α - β) := by
    rw [hα, hβ, hT, ← map_sub]
    refine IsUnit.map j (WittVector.isUnit_of_coeff_zero_ne_zero _ ?_)
    rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
    exact sub_ne_zero.mpr hζp.symm
  obtain ⟨ui, hui⟩ := hd.exists_left_inv

  have huiR : ui * (j (WittVector.teichmuller p ζ) - j (WittVector.teichmuller p (ζ ^ p))) = 1 := by
    rw [← hT, ← hα, ← hβ]; exact hui
  obtain ⟨hK0, hK1⟩ := X2R.lie_eq_ker hp j X ρ hρ ζ hgen ui huiR
  have huiS : π ui * ((π.comp j) (WittVector.teichmuller p ζ) - (π.comp j) (WittVector.teichmuller p (ζ ^ p))) = 1 := by
    rw [RingHom.comp_apply, RingHom.comp_apply, ← map_sub, ← map_mul, huiR, map_one]
  obtain ⟨hK0', hK1'⟩ := X2R.lie_eq_ker hpS (π.comp j) (X.map π) ρ' hρ' ζ hgen (π ui) huiS
  rw [← hT] at hK0 hK1 hK0' hK1'
  rw [← hα] at hK0
  rw [← hβ] at hK1

  set Z : Matrix (Fin 2) (Fin 2) R := ρ T with hZ
  set e₁ : Matrix (Fin 2) (Fin 2) R := ui • (α • (1 : Matrix (Fin 2) (Fin 2) R) - Z) with he₁
  set e₀ : Matrix (Fin 2) (Fin 2) R := ui • (Z - β • (1 : Matrix (Fin 2) (Fin 2) R)) with he₀
  have hmap1 : ∀ x : R, (x • (1 : Matrix (Fin 2) (Fin 2) R)).map π = π x • (1 : Matrix (Fin 2) (Fin 2) S) := by
    intro x; ext i k
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs <;> simp [hZ]
  have he1map : π ui • ((π.comp j) T • (1 : Matrix (Fin 2) (Fin 2) S) - ρ' T) = e₁.map π := by
    rw [hρmap, he₁]
    ext i k
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply, RingHom.comp_apply,
      smul_eq_mul, map_mul, map_sub, hα]
    split_ifs <;> simp [hZ]
  have he0map : π ui • (ρ' T - (π.comp j) (WittVector.teichmuller p (ζ ^ p)) • (1 : Matrix (Fin 2) (Fin 2) S)) = e₀.map π := by
    rw [hρmap, he₀]
    ext i k
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply, RingHom.comp_apply,
      smul_eq_mul, map_mul, map_sub, hβ]
    split_ifs <;> simp [hZ]
  rw [he1map] at hK0'
  rw [he0map] at hK1'

  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 2 two_ne_zero]
  have hσσ : ∀ a : Zp2 p, WittVector.frobenius (WittVector.frobenius a) = a := fun a => by
    ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul, ← pow_two, ← hcard,
      FiniteField.pow_card]
  have ht : WittVector.frobenius (T + WittVector.frobenius T) = T + WittVector.frobenius T := by
    rw [map_add, hσσ, add_comm]
  have hn : WittVector.frobenius (T * WittVector.frobenius T) = T * WittVector.frobenius T := by
    rw [map_mul, hσσ, mul_comm]
  have hαβ : j (T + WittVector.frobenius T) = α + β := by rw [map_add, hα, hβ, hTp]
  have hαβ' : j (T * WittVector.frobenius T) = α * β := by rw [map_mul, hα, hβ, hTp]
  have qt := WittVector.ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent p hp ρ j _ ht
  have qn := WittVector.ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent p hp ρ j _ hn
  rw [Algebra.algebraMap_eq_smul_one, hαβ] at qt
  rw [Algebra.algebraMap_eq_smul_one, hαβ'] at qn
  have hrel0 : Z * Z - (α + β) • Z + (α * β) • (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
    have key : T * T - (T + WittVector.frobenius T) * T + T * WittVector.frobenius T = 0 := by ring
    have := congrArg ρ key
    rw [map_add, map_sub, qn, map_mul, map_mul, qt, map_zero, smul_mul_assoc, one_mul] at this
    rw [hZ]; exact this
  have hrel : (Z - α • (1 : Matrix (Fin 2) (Fin 2) R)) * (Z - β • 1) = 0 := by
    rw [← hrel0]
    simp only [sub_mul, mul_sub, smul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, add_smul, mul_comm β α]
    abel
  have hrel' : (Z - β • (1 : Matrix (Fin 2) (Fin 2) R)) * (Z - α • 1) = 0 := by
    rw [← hrel0]
    simp only [sub_mul, mul_sub, smul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, add_smul, mul_comm β α]
    abel
  have hsum : e₀ + e₁ = 1 := by
    rw [he₀, he₁, ← smul_add,
      show (Z - β • (1 : Matrix (Fin 2) (Fin 2) R)) + (α • 1 - Z) = (α - β) • 1 by rw [sub_smul]; abel,
      smul_smul, hui, one_smul]
  have h10 : e₁ * e₀ = 0 := by
    rw [he₁, he₀, smul_mul_assoc, mul_smul_comm, smul_smul, ← neg_sub Z, neg_mul, hrel, neg_zero, smul_zero]
  have h01 : e₀ * e₁ = 0 := by
    rw [he₀, he₁, smul_mul_assoc, mul_smul_comm, smul_smul, ← neg_sub Z, mul_neg, hrel', neg_zero, smul_zero]
  have hidem : IsIdempotentElem (Matrix.mulVecLin e₀) := by
    change Matrix.mulVecLin e₀ ∘ₗ Matrix.mulVecLin e₀ = Matrix.mulVecLin e₀
    rw [← Matrix.mulVecLin_mul]
    congr 1
    have : e₀ * (e₀ + e₁) = e₀ := by rw [hsum, mul_one]
    rwa [mul_add, h01, add_zero] at this
  have hker_range : LinearMap.ker (Matrix.mulVecLin e₁) = LinearMap.range (Matrix.mulVecLin e₀) := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · intro hv
      refine ⟨v, ?_⟩
      rw [Matrix.mulVecLin_apply]
      have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M *ᵥ v) hsum
      simp only [Matrix.add_mulVec, hv, add_zero, Matrix.one_mulVec] at h1
      exact h1
    · rintro ⟨w, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h10, Matrix.zero_mulVec]

  show IsCompl (X.lieZero j) (X.lieOne j) ∧ Module.Invertible R ↥(X.lieZero j) ∧ Module.Invertible R ↥(X.lieOne j)
  rw [hK0, hK1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hker_range]; exact LinearMap.IsIdempotentElem.isCompl hidem
  · have hinv : Module.Invertible S ↥(LinearMap.ker (Matrix.mulVecLin (e₁.map (algebraMap R S)))) := by
      have := h.2.1; rw [hK0'] at this; exact this
    exact X2R.invertible_ker hπ' hker' e₀ e₁ hsum h10 hinv
  · have hinv : Module.Invertible S ↥(LinearMap.ker (Matrix.mulVecLin (e₀.map (algebraMap R S)))) := by
      have := h.2.2; rw [hK1'] at this; exact this
    exact X2R.invertible_ker hπ' hker' e₁ e₀ (by rw [add_comm]; exact hsum) h01 hinv

end S_CerednikDrinfeld_FormalODModule_isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent (solution)
