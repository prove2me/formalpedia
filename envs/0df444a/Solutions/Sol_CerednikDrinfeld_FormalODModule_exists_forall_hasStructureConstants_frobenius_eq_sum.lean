-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_forall_hasStructureConstants_frobenius_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ef01509e-d9df-5b23-880d-777f6f69d881

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Theorems.Thm_WittVector_exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem
import Theorems.Thm_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_forall_hasStructureConstants_frobenius_eq_sum

set_option autoImplicit false

universe u

open MvPowerSeries

namespace FFromPi

section W1

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

open MvFormalGroup MvFormalGroup.WittLaw in

theorem mulFam_verschiebung_eq (w : WittVector p R) (n : ℕ) :
    mulFam p (WittVector.verschiebung w) n =
      subst (fun k => subst (frobPolyFam p R) (mulFam p w k)) (verFam R n) := by
  have hcV : cVec p (τ := ℕ) (WittVector.verschiebung w) = WittVector.verschiebung (cVec p w) :=
    WittVector.map_verschiebung _ w
  have hL : mulFam p (WittVector.verschiebung w) n =
      (((WittVector.verschiebung (cVec p w * WittVector.frobenius (xTaut p R))).coeff n :
        MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
    rw [mulFam_apply, WittVector.verschiebung_mul_frobenius, ← hcV]
    rfl
  have hR : ∀ k, subst (frobPolyFam p R) (mulFam p w k) =
      (((cVec p w * WittVector.frobenius (xTaut p R)).coeff k : MvPolynomial ℕ R) :
        MvPowerSeries ℕ R) := by
    intro k
    have hf : frobPolyFam p R = fun m => (frobPoly p R m : MvPowerSeries ℕ R) := rfl
    rw [hf, mulFam_apply, ← WittLaw.coe_aeval, aeval_mulPoly, mk_frobPoly]
  have hS : HasSubst (fun k => subst (frobPolyFam p R) (mulFam p w k)) := by
    have h := (hasSubst_mulFam (p := p) w).comp (hasSubst_frobPolyFam (p := p) (R := R))
    simpa only [coe_substAlgHom] using h
  rw [hL]
  cases n with
  | zero =>
    rw [WittVector.verschiebung_coeff_zero, verFam_zero, MvPolynomial.coe_zero]
    rw [← coe_substAlgHom hS, map_zero]
  | succ k =>
    rw [WittVector.verschiebung_coeff_succ, verFam_succ, subst_X hS, hR]

open MvFormalGroup MvFormalGroup.CartierModule in

theorem verschiebung_smul_eq {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]
    (w : WittVector p R) (f : CartierModule p Φ) :
    WittVector.verschiebung w • f = verschiebungInt (w • frobenius f) := by
  apply CartierModule.ext
  funext j
  show subst (WittLaw.mulFam p (WittVector.verschiebung w)) (f.toPowerSeries j) =
    subst (WittLaw.frobPolyFam p R) (subst (WittLaw.mulFam p w)
      (subst (WittLaw.verFam R) (f.toPowerSeries j)))
  have hS : HasSubst (fun k => subst (WittLaw.frobPolyFam p R) (WittLaw.mulFam p w k)) := by
    have h := (WittLaw.hasSubst_mulFam (p := p) w).comp (WittLaw.hasSubst_frobPolyFam (p := p) (R := R))
    simpa only [coe_substAlgHom] using h
  rw [subst_comp_subst_apply (WittLaw.hasSubst_mulFam w) WittLaw.hasSubst_frobPolyFam,
    subst_comp_subst_apply WittLaw.hasSubst_verFam hS]
  congr 1
  funext n
  exact mulFam_verschiebung_eq w n

end W1

section W2

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

theorem eq_teichmuller_add_verschiebung_shift (w : WittVector p R) :
    w = WittVector.teichmuller p (w.coeff 0) + WittVector.verschiebung (w.shift 1) := by
  have h := WittVector.init_add_tail w 1
  have hi : WittVector.init 1 w = WittVector.teichmuller p (w.coeff 0) := by
    ext n
    simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos p (w.coeff 0) (n + 1) (Nat.succ_pos n)]
  have ht : WittVector.tail 1 w = WittVector.verschiebung (w.shift 1) := by
    ext n
    simp only [WittVector.tail, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.verschiebung_coeff_zero]
    | succ n => simp [WittVector.verschiebung_coeff_succ, WittVector.shift_coeff, Nat.add_comm]
  rw [hi, ht] at h
  exact h.symm

open MvFormalGroup MvFormalGroup.CartierModule in

theorem smul_eq_homothety_add {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]
    (w : WittVector p R) (f : CartierModule p Φ) :
    w • f = homothety (w.coeff 0) f + verschiebungInt (w.shift 1 • frobenius f) := by
  conv_lhs => rw [eq_teichmuller_add_verschiebung_shift w]
  rw [add_smul, teichmuller_smul, verschiebung_smul_eq]

end W2

section W3

variable (p : ℕ) [hp : Fact p.Prime]

theorem ghostComponent_eq_of_coeff_eq {R : Type u} [CommRing R] (n : ℕ) (x y : WittVector p R)
    (h : ∀ i ≤ n, x.coeff i = y.coeff i) :
    WittVector.ghostComponent n x = WittVector.ghostComponent n y := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, aeval_wittPolynomial,
    aeval_wittPolynomial]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

theorem exists_natCast_eq_teichmuller_add_verschiebung_unit :
    ∃ η θ : WittVector p (PadicInt p),
      (p : WittVector p (PadicInt p)) =
        WittVector.teichmuller p (p : PadicInt p) + WittVector.verschiebung η ∧ θ * η = 1 := by
  have hp0 : (p : PadicInt p) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hpnz : (p : PadicInt p) ∈ nonZeroDivisors (PadicInt p) := mem_nonZeroDivisors_of_ne_zero hp0
  set y : WittVector p (PadicInt p) :=
    (p : WittVector p (PadicInt p)) - WittVector.teichmuller p (p : PadicInt p) with hy
  set η : WittVector p (PadicInt p) := y.shift 1 with hη
  have hyV : WittVector.verschiebung η = y := by
    have := eq_teichmuller_add_verschiebung_shift (p := p) y
    have hy0 : y.coeff 0 = 0 := by
      have h1 := (WittVector.constantCoeff : WittVector p (PadicInt p) →+* PadicInt p).map_sub
        (p : WittVector p (PadicInt p)) (WittVector.teichmuller p (p : PadicInt p))
      have h2 : (WittVector.constantCoeff : WittVector p (PadicInt p) →+* PadicInt p)
          (p : WittVector p (PadicInt p)) = p := map_natCast _ p
      rw [h2] at h1
      rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.teichmuller_coeff_zero, sub_self] at h1
      rw [hy]; exact h1
    rw [hy0, WittVector.teichmuller_zero, zero_add] at this
    rw [hη]; exact this.symm

  have hgη : ∀ k, WittVector.ghostComponent k η = 1 - (p : PadicInt p) ^ (p ^ (k + 1) - 1) := by
    intro k
    have h := congrArg (WittVector.ghostComponent (k + 1)) hyV
    rw [WittVector.ghostComponent_verschiebung, hy, map_sub, map_natCast,
      WittVector.ghostComponent_teichmuller] at h
    have hk : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ hp.out.pos
    have h2 : (p : PadicInt p) * WittVector.ghostComponent k η =
        p * (1 - (p : PadicInt p) ^ (p ^ (k + 1) - 1)) := by
      rw [h, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hk]
    exact mul_left_cancel₀ hp0 h2

  have hle : ∀ k : ℕ, k + 1 ≤ p ^ (k + 1) - 1 := fun k =>
    Nat.le_sub_one_of_lt (Nat.lt_pow_self hp.out.one_lt)
  have hu : ∀ k : ℕ, IsUnit (1 - (p : PadicInt p) ^ (p ^ (k + 1) - 1)) := by
    intro k
    have hmem : (p : PadicInt p) ^ (p ^ (k + 1) - 1) ∈ nonunits (PadicInt p) := by
      rw [← IsLocalRing.mem_maximalIdeal, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (Nat.lt_of_lt_of_le (Nat.succ_pos k) (hle k))
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hmem
  set g : ℕ → PadicInt p := fun k => ((hu k).unit⁻¹ : (PadicInt p)ˣ) with hg
  have hgu : ∀ k, g k * (1 - (p : PadicInt p) ^ (p ^ (k + 1) - 1)) = 1 := by
    intro k
    have h1 := (hu k).unit.inv_mul
    rw [IsUnit.unit_spec] at h1
    exact h1

  have hσ : ∀ a : PadicInt p, (RingHom.id (PadicInt p)) a - a ^ p ∈ Ideal.span {(p : PadicInt p)} := by
    intro a
    rw [RingHom.id_apply, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker,
      map_sub, map_pow, ZMod.pow_card, sub_self]
  have hpowmem : ∀ k m : ℕ, k + 1 ≤ m →
      (p : PadicInt p) ^ m ∈ Ideal.span {(p : PadicInt p) ^ (k + 1)} := fun k m hkm =>
    Ideal.mem_span_singleton.mpr (pow_dvd_pow _ hkm)
  have hgc : ∀ k : ℕ, k + 1 < 0 + (0 : ℕ) + (k + 2) →
      g (k + 1) - (RingHom.id (PadicInt p)) (g k) ∈ Ideal.span {(p : PadicInt p) ^ (k + 1)} := by
    intro k _
    rw [RingHom.id_apply]
    have key : g (k + 1) - g k = g (k + 1) * g k *
        ((p : PadicInt p) ^ (p ^ (k + 2) - 1) - (p : PadicInt p) ^ (p ^ (k + 1) - 1)) := by
      have a1 := hgu k
      have a2 := hgu (k + 1)
      linear_combination (-(g (k + 1))) * a1 + (g k) * a2
    rw [key]
    refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ ?_ ?_)
    · exact hpowmem k _ ((hle k).trans (Nat.sub_le_sub_right
        (Nat.pow_le_pow_right hp.out.pos (Nat.le_succ _)) 1))
    · exact hpowmem k _ (hle k)
  have hex : ∀ n : ℕ, ∃ x : WittVector p (PadicInt p), ∀ k < n, WittVector.ghostComponent k x = g k :=
    fun n => WittVector.exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem p (RingHom.id _) hσ n g
      (fun k _ => hgc k (by omega))
  choose xs hxs using hex
  set θ : WittVector p (PadicInt p) := WittVector.mk p fun k => (xs (k + 1)).coeff k with hθ
  have hθcoeff : ∀ n k, k < n → θ.coeff k = (xs n).coeff k := by
    intro n k hk
    have h1 := WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hpnz (k + 1) (xs (k + 1)) (xs n)
      (fun i hi => by rw [hxs (k + 1) i hi, hxs n i (by omega)]) k (Nat.lt_succ_self k)
    rw [← h1, hθ, WittVector.coeff_mk]
  have hgθ : ∀ k, WittVector.ghostComponent k θ = g k := by
    intro k
    rw [ghostComponent_eq_of_coeff_eq p k θ (xs (k + 1)) (fun i hi => hθcoeff (k + 1) i (Nat.lt_succ_of_le hi)),
      hxs (k + 1) k (Nat.lt_succ_self k)]
  refine ⟨η, θ, ?_, ?_⟩
  · rw [hyV, hy, add_sub_cancel]
  · ext k
    exact WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hpnz (k + 1) (θ * η) 1
      (fun i _ => by rw [map_mul, hgθ, hgη, map_one, hgu]) k (Nat.lt_succ_self k)

theorem exists_natCast_eq_teichmuller_add_verschiebung_unit_map
    {B : Type u} [CommRing B] [Algebra (PadicInt p) B] :
    ∃ η θ : WittVector p B,
      (p : WittVector p B) = WittVector.teichmuller p (p : B) + WittVector.verschiebung η ∧ θ * η = 1 := by
  obtain ⟨η, θ, h1, h2⟩ := exists_natCast_eq_teichmuller_add_verschiebung_unit p
  refine ⟨WittVector.map (algebraMap (PadicInt p) B) η, WittVector.map (algebraMap (PadicInt p) B) θ, ?_, ?_⟩
  · have h := congrArg (WittVector.map (algebraMap (PadicInt p) B)) h1
    rw [map_natCast, map_add, WittVector.map_teichmuller, WittVector.map_verschiebung, map_natCast] at h
    exact h
  · rw [← map_mul, h2, map_one]

end W3

section Transfer

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

open MvFormalGroup MvFormalGroup.CartierModule

section ev

variable {d : ℕ} {Φ : MvFormalGroup d B} [Φ.IsComm]

local notation "VV" => (verschiebungInt (p := p) (Φ := Φ))

noncomputable def ev (δ : Fin 2 → CartierModule p Φ) (K : ℕ) (c : ℕ → Fin 2 → B) : CartierModule p Φ :=
  ∑ m ∈ Finset.range K, (⇑VV)^[m] (∑ k : Fin 2, homothety (c m k) (δ k))

def scons (e : Fin 2 → B) (c : ℕ → Fin 2 → B) : ℕ → Fin 2 → B := fun m => Nat.casesOn m e c

omit [CommRing B] in
@[scoped simp] theorem scons_zero (e : Fin 2 → B) (c : ℕ → Fin 2 → B) : scons e c 0 = e := rfl
omit [CommRing B] in
@[scoped simp] theorem scons_succ (e : Fin 2 → B) (c : ℕ → Fin 2 → B) (m : ℕ) : scons e c (m + 1) = c m := rfl

theorem iterate_V_add' (N : ℕ) (a b : CartierModule p Φ) : (⇑VV)^[N] (a + b) = (⇑VV)^[N] a + (⇑VV)^[N] b := by
  induction N generalizing a b with
  | zero => rfl
  | succ N ih => simp only [Function.iterate_succ_apply', ih, map_add]

theorem iterate_V_zero' (N : ℕ) : (⇑VV)^[N] (0 : CartierModule p Φ) = 0 :=
  Function.iterate_fixed (map_zero _) N

theorem iterate_V_sum' {ι : Type*} (s : Finset ι) (N : ℕ) (a : ι → CartierModule p Φ) :
    (⇑VV)^[N] (∑ i ∈ s, a i) = ∑ i ∈ s, (⇑VV)^[N] (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Function.iterate_fixed (map_zero _) N]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, iterate_V_add', ih]

theorem homothety_iterate_V' (N : ℕ) (b : B) (a : CartierModule p Φ) :
    homothety b ((⇑VV)^[N] a) = (⇑VV)^[N] (homothety (b ^ p ^ N) a) := by
  induction N generalizing b a with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', homothety_verschiebungInt, ih, Function.iterate_succ_apply',
      ← pow_mul, ← pow_succ']

theorem ev_zero (δ : Fin 2 → CartierModule p Φ) (c : ℕ → Fin 2 → B) : ev δ 0 c = 0 := by
  simp [ev]

theorem ev_succ (δ : Fin 2 → CartierModule p Φ) (K : ℕ) (c : ℕ → Fin 2 → B) :
    ev δ (K + 1) c = (∑ k : Fin 2, homothety (c 0 k) (δ k)) + verschiebungInt (ev δ K (fun m => c (m + 1))) := by
  rw [ev, Finset.sum_range_succ', ev, map_sum]
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
  rw [add_comm]

theorem ev_scons (δ : Fin 2 → CartierModule p Φ) (K : ℕ) (e : Fin 2 → B) (c : ℕ → Fin 2 → B) :
    ev δ (K + 1) (scons e c) = (∑ k : Fin 2, homothety (e k) (δ k)) + verschiebungInt (ev δ K c) := by
  rw [ev_succ]; rfl

theorem ev_const_zero (δ : Fin 2 → CartierModule p Φ) (K : ℕ) : ev δ K (fun _ _ => 0) = 0 := by
  simp [ev, homothety_zero_left]

theorem ev_add (δ : Fin 2 → CartierModule p Φ) (K L : ℕ) (c : ℕ → Fin 2 → B) :
    ∃ r, ev δ (K + L) c = ev δ K c + (⇑VV)^[K] r := by
  induction K generalizing c with
  | zero => exact ⟨ev δ (0 + L) c, by simp [ev_zero]⟩
  | succ K ih =>
    obtain ⟨r, hr⟩ := ih (fun m => c (m + 1))
    refine ⟨r, ?_⟩
    rw [Nat.succ_add, ev_succ, ev_succ, hr, map_add, Function.iterate_succ_apply', add_assoc]

theorem ev_congr (δ : Fin 2 → CartierModule p Φ) (N : ℕ) (c c' : ℕ → Fin 2 → B)
    (h : ∀ m, m < N → c m = c' m) : ev δ N c = ev δ N c' :=
  Finset.sum_congr rfl fun m hm => by rw [h m (Finset.mem_range.mp hm)]

theorem ev_eq_fin_sum (δ : Fin 2 → CartierModule p Φ) (N : ℕ) (c : ℕ → Fin 2 → B) :
    ev δ N c = ∑ m : Fin N, (⇑VV)^[(m : ℕ)] (∑ k : Fin 2, homothety (c m k) (δ k)) :=
  (Fin.sum_univ_eq_sum_range (fun m => (⇑VV)^[m] (∑ k : Fin 2, homothety (c m k) (δ k))) N).symm

end ev

section S

variable (X X' : CerednikDrinfeld.FormalODModule p B)
  (γ : Fin 2 → CartierModule p X.F) (γ' : Fin 2 → CartierModule p X'.F)

local notation "VX" => (verschiebungInt (p := p) (Φ := X.F))
local notation "VX'" => (verschiebungInt (p := p) (Φ := X'.F))

def S (K : ℕ) : Set (CartierModule p X.F × CartierModule p X'.F) :=
  {q | ∃ (c : ℕ → Fin 2 → B) (h : CartierModule p X.F) (h' : CartierModule p X'.F),
    q.1 = ev γ K c + (⇑VX)^[K] h ∧ q.2 = ev γ' K c + (⇑VX')^[K] h'}

theorem mem_S_zero (q : CartierModule p X.F × CartierModule p X'.F) : q ∈ S X X' γ γ' 0 :=
  ⟨fun _ _ => 0, q.1, q.2, by simp [ev_zero], by simp [ev_zero]⟩

theorem mem_S_iterate (K : ℕ) (h : CartierModule p X.F) (h' : CartierModule p X'.F) :
    ((⇑VX)^[K] h, (⇑VX')^[K] h') ∈ S X X' γ γ' K :=
  ⟨fun _ _ => 0, h, h', by rw [ev_const_zero, zero_add], by rw [ev_const_zero, zero_add]⟩

theorem mem_S_cons {K : ℕ} {z : CartierModule p X.F} {z' : CartierModule p X'.F}
    (hz : (z, z') ∈ S X X' γ γ' K) (e : Fin 2 → B) :
    ((∑ k : Fin 2, homothety (e k) (γ k)) + verschiebungInt z,
      (∑ k : Fin 2, homothety (e k) (γ' k)) + verschiebungInt z') ∈ S X X' γ γ' (K + 1) := by
  obtain ⟨c, h, h', h1, h2⟩ := hz
  simp only at h1 h2
  refine ⟨scons e c, h, h', ?_, ?_⟩
  · show _ = _
    rw [h1, map_add, ev_scons, Function.iterate_succ_apply', add_assoc]
  · show _ = _
    rw [h2, map_add, ev_scons, Function.iterate_succ_apply', add_assoc]

theorem mem_S_uncons {K : ℕ} {x : CartierModule p X.F} {x' : CartierModule p X'.F}
    (hx : (x, x') ∈ S X X' γ γ' (K + 1)) :
    ∃ (e : Fin 2 → B) (z : CartierModule p X.F) (z' : CartierModule p X'.F),
      (z, z') ∈ S X X' γ γ' K ∧ x = (∑ k : Fin 2, homothety (e k) (γ k)) + verschiebungInt z ∧
        x' = (∑ k : Fin 2, homothety (e k) (γ' k)) + verschiebungInt z' := by
  obtain ⟨c, h, h', h1, h2⟩ := hx
  simp only at h1 h2
  refine ⟨c 0, ev γ K (fun m => c (m + 1)) + (⇑VX)^[K] h, ev γ' K (fun m => c (m + 1)) + (⇑VX')^[K] h',
    ⟨fun m => c (m + 1), h, h', rfl, rfl⟩, ?_, ?_⟩
  · rw [h1, ev_succ, map_add, Function.iterate_succ_apply', add_assoc]
  · rw [h2, ev_succ, map_add, Function.iterate_succ_apply', add_assoc]

theorem mem_S_V {K : ℕ} {z : CartierModule p X.F} {z' : CartierModule p X'.F}
    (hz : (z, z') ∈ S X X' γ γ' K) :
    (verschiebungInt z, verschiebungInt z') ∈ S X X' γ γ' (K + 1) := by
  have h := mem_S_cons X X' γ γ' hz (fun _ => 0)
  simpa [homothety_zero_left] using h

theorem mem_S_homothety (K : ℕ) : ∀ (b : B) {x : CartierModule p X.F} {x' : CartierModule p X'.F},
    (x, x') ∈ S X X' γ γ' K → (homothety b x, homothety b x') ∈ S X X' γ γ' K := by
  induction K with
  | zero => exact fun b _ _ _ => mem_S_zero X X' γ γ' _
  | succ K ih =>
    intro b x x' hx
    obtain ⟨e, z, z', hz, h1, h2⟩ := mem_S_uncons X X' γ γ' hx
    have key := mem_S_cons X X' γ γ' (ih (b ^ p) hz) (fun k => b * e k)
    rw [h1, h2]
    simpa only [map_add, map_sum, ← homothety_mul, homothety_verschiebungInt] using key

theorem mem_S_mono {K : ℕ} {x : CartierModule p X.F} {x' : CartierModule p X'.F}
    (hx : (x, x') ∈ S X X' γ γ' (K + 1)) : (x, x') ∈ S X X' γ γ' K := by
  obtain ⟨c, h, h', h1, h2⟩ := hx
  obtain ⟨r, hr⟩ := ev_add γ K 1 c
  obtain ⟨r', hr'⟩ := ev_add γ' K 1 c
  refine ⟨c, r + verschiebungInt h, r' + verschiebungInt h', ?_, ?_⟩
  · rw [h1, hr, iterate_V_add', add_assoc, Function.iterate_succ_apply]
  · rw [h2, hr', iterate_V_add', add_assoc, Function.iterate_succ_apply]

end S

section Good

open CerednikDrinfeld

variable (X X' : FormalODModule p B) (γ : Fin 2 → CartierModule p X.F) (γ' : Fin 2 → CartierModule p X'.F)

structure Good (K : ℕ) : Prop where
  add : ∀ {x y : CartierModule p X.F} {x' y' : CartierModule p X'.F},
    (x, x') ∈ S X X' γ γ' K → (y, y') ∈ S X X' γ γ' K → (x + y, x' + y') ∈ S X X' γ γ' K
  smul : ∀ (w : WittVector p B) {x : CartierModule p X.F} {x' : CartierModule p X'.F},
    (x, x') ∈ S X X' γ γ' K → (w • x, w • x') ∈ S X X' γ γ' K
  pi : ∀ {x : CartierModule p X.F} {x' : CartierModule p X'.F},
    (x, x') ∈ S X X' γ γ' K → (endAct X.varpiEnd x, endAct X'.varpiEnd x') ∈ S X X' γ γ' K
  frobγ : ∀ i : Fin 2, (frobenius (γ i), frobenius (γ' i)) ∈ S X X' γ γ' K
  frob : ∀ {x : CartierModule p X.F} {x' : CartierModule p X'.F},
    (x, x') ∈ S X X' γ γ' (K + 1) → (frobenius x, frobenius x') ∈ S X X' γ γ' K

theorem good_zero : Good X X' γ γ' 0 :=
  ⟨fun _ _ => mem_S_zero X X' γ γ' _, fun _ _ _ _ => mem_S_zero X X' γ γ' _,
    fun _ => mem_S_zero X X' γ γ' _, fun _ => mem_S_zero X X' γ γ' _, fun _ => mem_S_zero X X' γ γ' _⟩

theorem zero_mem_S (K : ℕ) : ((0 : CartierModule p X.F), (0 : CartierModule p X'.F)) ∈ S X X' γ γ' K := by
  have h := mem_S_iterate X X' γ γ' K 0 0
  rwa [iterate_V_zero', iterate_V_zero'] at h

theorem Good.sum_mem {K : ℕ} (hK : Good X X' γ γ' K) {ι : Type*} (s : Finset ι)
    (f : ι → CartierModule p X.F) (f' : ι → CartierModule p X'.F)
    (h : ∀ i ∈ s, (f i, f' i) ∈ S X X' γ γ' K) :
    (∑ i ∈ s, f i, ∑ i ∈ s, f' i) ∈ S X X' γ γ' K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_S X X' γ γ' K
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact hK.add (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

omit X' γ γ' in
theorem sum_homothety_ite {d : ℕ} {Φ : MvFormalGroup d B} [Φ.IsComm] (δ : Fin 2 → CartierModule p Φ)
    (jj : Fin 2) (b : B) :
    ∑ k : Fin 2, homothety (if k = jj then b else 0) (δ k) = homothety b (δ jj) := by
  rw [Finset.sum_eq_single jj]
  · rw [if_pos rfl]
  · intro k _ hk
    rw [if_neg hk, homothety_zero_left]
  · intro h; exact absurd (Finset.mem_univ jj) h

variable {a : ℕ → Fin 2 → B}

theorem pi_basis (ha : X.HasStructureConstants γ a) (ha' : X'.HasStructureConstants γ' a)
    (J : ℕ) (i : Fin 2) :
    ∃ (t : CartierModule p X.F) (t' : CartierModule p X'.F), (t, t') ∈ S X X' γ γ' J ∧
      endAct X.varpiEnd (γ i) =
        homothety (a 0 i) (γ (FormalODModule.piIndex 0 i)) + verschiebungInt t ∧
      endAct X'.varpiEnd (γ' i) =
        homothety (a 0 i) (γ' (FormalODModule.piIndex 0 i)) + verschiebungInt t' := by
  obtain ⟨r, hr⟩ := ha i (J + 1)
  obtain ⟨r', hr'⟩ := ha' i (J + 1)
  set c : ℕ → Fin 2 → B := fun m k => if k = FormalODModule.piIndex (m + 1) i then a (m + 1) i else 0
    with hc
  refine ⟨ev γ J c + (⇑(verschiebungInt (p := p) (Φ := X.F)))^[J] r,
    ev γ' J c + (⇑(verschiebungInt (p := p) (Φ := X'.F)))^[J] r', ⟨c, r, r', rfl, rfl⟩, ?_, ?_⟩
  · rw [hr, Fin.sum_univ_eq_sum_range (fun m => (⇑(verschiebungInt (p := p) (Φ := X.F)))^[m]
      (homothety (a m i) (γ (FormalODModule.piIndex m i)))) (J + 1), Finset.sum_range_succ']
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply', map_add, ev, map_sum, hc,
      sum_homothety_ite]
    abel
  · rw [hr', Fin.sum_univ_eq_sum_range (fun m => (⇑(verschiebungInt (p := p) (Φ := X'.F)))^[m]
      (homothety (a m i) (γ' (FormalODModule.piIndex m i)))) (J + 1), Finset.sum_range_succ']
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply', map_add, ev, map_sum, hc,
      sum_homothety_ite]
    abel

theorem pi_basis_mem (ha : X.HasStructureConstants γ a) (ha' : X'.HasStructureConstants γ' a)
    (J : ℕ) (i : Fin 2) :
    (endAct X.varpiEnd (γ i), endAct X'.varpiEnd (γ' i)) ∈ S X X' γ γ' (J + 1) := by
  obtain ⟨t, t', ht, h1, h2⟩ := pi_basis X X' γ γ' ha ha' J i
  have key := mem_S_cons X X' γ γ' ht (fun k => if k = FormalODModule.piIndex 0 i then a 0 i else 0)
  rw [sum_homothety_ite, sum_homothety_ite] at key
  rwa [h1, h2]

omit X X' γ γ' in
theorem piIndex_zero_piIndex_zero (i : Fin 2) :
    FormalODModule.piIndex 0 (FormalODModule.piIndex 0 i) = i := by
  ext; simp only [FormalODModule.piIndex_val]; omega

omit X' γ γ' in
theorem endAct_varpiEnd_varpiEnd (f : CartierModule p X.F) :
    endAct X.varpiEnd (endAct X.varpiEnd f) = p • f := by
  have h : X.varpiEnd * X.varpiEnd = (p : MvFormalGroup.End X.F) := by
    rw [FormalODModule.varpiEnd_mul_varpiEnd]; exact map_natCast X.actRingHom p
  have h2 : endAct (X.varpiEnd * X.varpiEnd) f = endAct X.varpiEnd (endAct X.varpiEnd f) := by
    rw [map_mul]; rfl
  rw [← h2, h, endAct_natCast]

theorem a_zero_mul {j : Zp2 p →+* B} (hγ : X.IsHomogeneousVBasis j γ)
    (ha : X.HasStructureConstants γ a) (ha' : X'.HasStructureConstants γ' a) (i : Fin 2) :
    a 0 i * a 0 (FormalODModule.piIndex 0 i) = p := by
  obtain ⟨t, t', -, h1, -⟩ := pi_basis X X' γ γ' ha ha' 0 i
  obtain ⟨t₂, t₂', -, h3, -⟩ := pi_basis X X' γ γ' ha ha' 0 (FormalODModule.piIndex 0 i)
  have key := endAct_varpiEnd_varpiEnd X (γ i)
  rw [h1, map_add, endAct_homothety, h3, endAct_verschiebungInt, piIndex_zero_piIndex_zero, map_add,
    ← homothety_mul, homothety_verschiebungInt] at key
  have ht := congrArg tangent key
  simp only [map_add, tangent_homothety, tangent_verschiebungInt, add_zero, map_nsmul] at ht
  set Mγ : Matrix (Fin 2) (Fin 2) B := Matrix.of fun i k => tangent (γ i) k with hM
  have hrow : ∀ k, (a 0 i * a 0 (FormalODModule.piIndex 0 i) - p) * Mγ i k = 0 := by
    intro k
    have h1 := congrArg (fun v : Fin 2 → B => v k) ht
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at h1
    rw [hM, Matrix.of_apply, sub_mul, h1, sub_self]
  have hunit : Mγ * Mγ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hγ.2
  set δ : B := a 0 i * a 0 (FormalODModule.piIndex 0 i) - p with hδdef
  have hc : δ = ∑ k : Fin 2, δ * Mγ i k * Mγ⁻¹ k i := by
    have h1 := congrArg (fun N : Matrix (Fin 2) (Fin 2) B => N i i) hunit
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    calc δ = δ * 1 := (mul_one δ).symm
      _ = δ * ∑ k : Fin 2, Mγ i k * Mγ⁻¹ k i := by rw [h1]
      _ = ∑ k : Fin 2, δ * Mγ i k * Mγ⁻¹ k i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
  have hδ : δ = 0 := by
    rw [hc]
    exact Finset.sum_eq_zero fun k _ => by rw [hrow k, zero_mul]
  exact sub_eq_zero.mp hδ

end Good

section Uniq

variable [Algebra (PadicInt p) B] {Φ : MvFormalGroup 2 B} [Φ.IsComm]
  (δ : Fin 2 → CartierModule p Φ) (hdet : IsUnit (Matrix.of fun i k => tangent (δ i) k).det)

include hdet in
theorem eq_of_sum_smul_tangent_eq (e e' : Fin 2 → B)
    (h : ∑ k : Fin 2, e k • tangent (δ k) = ∑ k : Fin 2, e' k • tangent (δ k)) : e = e' := by
  set Mδ : Matrix (Fin 2) (Fin 2) B := Matrix.of fun i k => tangent (δ i) k with hM
  have hvec : Matrix.vecMul e Mδ = Matrix.vecMul e' Mδ := by
    funext jj
    have h1 := congrArg (fun v : Fin 2 → B => v jj) h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    simpa [Matrix.vecMul, dotProduct, hM, Matrix.of_apply] using h1
  have h2 := congrArg (fun v => Matrix.vecMul v Mδ⁻¹) hvec
  rwa [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one,
    Matrix.vecMul_one] at h2

include hdet in
theorem ev_unique : ∀ (N : ℕ) (c c' : ℕ → Fin 2 → B) (h h' : CartierModule p Φ),
    ev δ N c + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] h =
      ev δ N c' + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] h' → ∀ m < N, c m = c' m := by
  have hVinj := verschiebungInt_injective_of_algebra_padicInt p Φ
  intro N
  induction N with
  | zero => intro _ _ _ _ _ m hm; exact absurd hm (Nat.not_lt_zero m)
  | succ N ih =>
    intro c c' h h' heq m hm
    rw [ev_succ, ev_succ, Function.iterate_succ_apply', Function.iterate_succ_apply', add_assoc, add_assoc,
      ← map_add, ← map_add] at heq
    have ht := congrArg tangent heq
    simp only [map_add, map_sum, tangent_homothety, tangent_verschiebungInt, add_zero] at ht
    have h0 : c 0 = c' 0 := eq_of_sum_smul_tangent_eq δ hdet _ _ ht
    rw [h0] at heq
    have heq2 := hVinj (add_left_cancel heq)
    have ih' := ih (fun m => c (m + 1)) (fun m => c' (m + 1)) h h' heq2
    rcases m with _ | m
    · exact h0
    · exact ih' m (by omega)

include hdet in

theorem digit_compat (cN : ℕ → ℕ → Fin 2 → B) (hN : ℕ → CartierModule p Φ) (x : CartierModule p Φ)
    (hcN : ∀ N, x = ev δ N (cN N) + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (hN N))
    (m N : ℕ) (hm : m < N) : cN N m = cN (m + 1) m := by
  obtain ⟨L, rfl⟩ : ∃ L, N = (m + 1) + L := ⟨N - (m + 1), by omega⟩
  obtain ⟨r, hr⟩ := ev_add δ (m + 1) L (cN (m + 1 + L))
  have e1 := hcN (m + 1 + L)
  rw [hr, Function.iterate_add_apply (⇑(verschiebungInt (p := p) (Φ := Φ))) (m + 1) L, add_assoc,
    ← iterate_V_add'] at e1
  exact ev_unique δ hdet (m + 1) _ _ _ _ (e1.symm.trans (hcN (m + 1))) m (Nat.lt_succ_self m)

end Uniq

section Succ

open CerednikDrinfeld

variable [Algebra (PadicInt p) B] (X X' : FormalODModule p B)
  (γ : Fin 2 → CartierModule p X.F) (γ' : Fin 2 → CartierModule p X'.F)

theorem sum_mem_of_add {K : ℕ}
    (hadd : ∀ {x y : CartierModule p X.F} {x' y' : CartierModule p X'.F},
      (x, x') ∈ S X X' γ γ' K → (y, y') ∈ S X X' γ γ' K → (x + y, x' + y') ∈ S X X' γ γ' K)
    {ι : Type*} (s : Finset ι) (f : ι → CartierModule p X.F) (f' : ι → CartierModule p X'.F)
    (h : ∀ i ∈ s, (f i, f' i) ∈ S X X' γ γ' K) :
    (∑ i ∈ s, f i, ∑ i ∈ s, f' i) ∈ S X X' γ γ' K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_S X X' γ γ' K
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact hadd (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

variable {K : ℕ} (hK : Good X X' γ γ' K)

include hK in
private theorem _root_.FFromPi.succ_add {x y : CartierModule p X.F} {x' y' : CartierModule p X'.F}
    (hx : (x, x') ∈ S X X' γ γ' (K + 1)) (hy : (y, y') ∈ S X X' γ γ' (K + 1)) :
    (x + y, x' + y') ∈ S X X' γ γ' (K + 1) := by
  obtain ⟨e, z, z', hz, hx1, hx2⟩ := mem_S_uncons X X' γ γ' hx
  obtain ⟨f, u, u', hu, hy1, hy2⟩ := mem_S_uncons X X' γ γ' hy
  set w : Fin 2 → WittVector p B := fun k => WittVector.teichmuller p (e k) + WittVector.teichmuller p (f k)
    with hw
  have inner : (z + u + ∑ k : Fin 2, (w k).shift 1 • frobenius (γ k),
      z' + u' + ∑ k : Fin 2, (w k).shift 1 • frobenius (γ' k)) ∈ S X X' γ γ' K :=
    hK.add (hK.add hz hu) (hK.sum_mem X X' γ γ' Finset.univ _ _ fun k _ => hK.smul _ (hK.frobγ k))
  have key := mem_S_cons X X' γ γ' inner (fun k => (w k).coeff 0)
  have hX : ∀ k, homothety (e k) (γ k) + homothety (f k) (γ k) =
      homothety ((w k).coeff 0) (γ k) + verschiebungInt ((w k).shift 1 • frobenius (γ k)) := by
    intro k
    rw [← teichmuller_smul, ← teichmuller_smul, ← add_smul, smul_eq_homothety_add]
  have hX' : ∀ k, homothety (e k) (γ' k) + homothety (f k) (γ' k) =
      homothety ((w k).coeff 0) (γ' k) + verschiebungInt ((w k).shift 1 • frobenius (γ' k)) := by
    intro k
    rw [← teichmuller_smul, ← teichmuller_smul, ← add_smul, smul_eq_homothety_add]
  have hC : (∑ k : Fin 2, homothety (e k) (γ k)) + verschiebungInt z +
      ((∑ k : Fin 2, homothety (f k) (γ k)) + verschiebungInt u) =
      (∑ k : Fin 2, homothety ((w k).coeff 0) (γ k)) +
        verschiebungInt (z + u + ∑ k : Fin 2, (w k).shift 1 • frobenius (γ k)) := by
    rw [add_add_add_comm, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun k _ => hX k,
      Finset.sum_add_distrib, map_add, map_add, map_sum, ← map_add]
    abel
  have hC' : (∑ k : Fin 2, homothety (e k) (γ' k)) + verschiebungInt z' +
      ((∑ k : Fin 2, homothety (f k) (γ' k)) + verschiebungInt u') =
      (∑ k : Fin 2, homothety ((w k).coeff 0) (γ' k)) +
        verschiebungInt (z' + u' + ∑ k : Fin 2, (w k).shift 1 • frobenius (γ' k)) := by
    rw [add_add_add_comm, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun k _ => hX' k,
      Finset.sum_add_distrib, map_add, map_add, map_sum, ← map_add]
    abel
  rw [hx1, hx2, hy1, hy2, hC, hC']
  exact key

p2m_export "FFromPi" "succ_add"
include hK in
theorem succ_smul (w : WittVector p B) {x : CartierModule p X.F} {x' : CartierModule p X'.F}
    (hx : (x, x') ∈ S X X' γ γ' (K + 1)) : (w • x, w • x') ∈ S X X' γ γ' (K + 1) := by
  obtain ⟨e, z, z', hz, hx1, hx2⟩ := mem_S_uncons X X' γ γ' hx
  set ww : Fin 2 → WittVector p B := fun k => w * WittVector.teichmuller p (e k) with hww
  have inner : ((∑ k : Fin 2, (ww k).shift 1 • frobenius (γ k)) + WittVector.frobenius w • z,
      (∑ k : Fin 2, (ww k).shift 1 • frobenius (γ' k)) + WittVector.frobenius w • z') ∈ S X X' γ γ' K :=
    hK.add (hK.sum_mem X X' γ γ' Finset.univ _ _ fun k _ => hK.smul _ (hK.frobγ k)) (hK.smul _ hz)
  have key := mem_S_cons X X' γ γ' inner (fun k => (ww k).coeff 0)
  have hX : ∀ k, w • homothety (e k) (γ k) =
      homothety ((ww k).coeff 0) (γ k) + verschiebungInt ((ww k).shift 1 • frobenius (γ k)) := by
    intro k
    rw [← teichmuller_smul, smul_smul, smul_eq_homothety_add]
  have hX' : ∀ k, w • homothety (e k) (γ' k) =
      homothety ((ww k).coeff 0) (γ' k) + verschiebungInt ((ww k).shift 1 • frobenius (γ' k)) := by
    intro k
    rw [← teichmuller_smul, smul_smul, smul_eq_homothety_add]
  have hC : w • ((∑ k : Fin 2, homothety (e k) (γ k)) + verschiebungInt z) =
      (∑ k : Fin 2, homothety ((ww k).coeff 0) (γ k)) +
        verschiebungInt ((∑ k : Fin 2, (ww k).shift 1 • frobenius (γ k)) + WittVector.frobenius w • z) := by
    rw [smul_add, Finset.smul_sum, smul_verschiebungInt, Finset.sum_congr rfl fun k _ => hX k,
      Finset.sum_add_distrib, map_add, map_sum]
    abel
  have hC' : w • ((∑ k : Fin 2, homothety (e k) (γ' k)) + verschiebungInt z') =
      (∑ k : Fin 2, homothety ((ww k).coeff 0) (γ' k)) +
        verschiebungInt ((∑ k : Fin 2, (ww k).shift 1 • frobenius (γ' k)) + WittVector.frobenius w • z') := by
    rw [smul_add, Finset.smul_sum, smul_verschiebungInt, Finset.sum_congr rfl fun k _ => hX' k,
      Finset.sum_add_distrib, map_add, map_sum]
    abel
  rw [hx1, hx2, hC, hC']
  exact key

variable {a : ℕ → Fin 2 → B} (ha : X.HasStructureConstants γ a) (ha' : X'.HasStructureConstants γ' a)
  (hAdd : ∀ {x y : CartierModule p X.F} {x' y' : CartierModule p X'.F},
      (x, x') ∈ S X X' γ γ' (K + 1) → (y, y') ∈ S X X' γ γ' (K + 1) → (x + y, x' + y') ∈ S X X' γ γ' (K + 1))
  (hSmul : ∀ (w : WittVector p B) {x : CartierModule p X.F} {x' : CartierModule p X'.F},
    (x, x') ∈ S X X' γ γ' (K + 1) → (w • x, w • x') ∈ S X X' γ γ' (K + 1))

include hK ha ha' hAdd in
theorem succ_pi {x : CartierModule p X.F} {x' : CartierModule p X'.F} (hx : (x, x') ∈ S X X' γ γ' (K + 1)) :
    (endAct X.varpiEnd x, endAct X'.varpiEnd x') ∈ S X X' γ γ' (K + 1) := by
  obtain ⟨e, z, z', hz, hx1, hx2⟩ := mem_S_uncons X X' γ γ' hx
  rw [hx1, hx2, map_add, map_add, map_sum, map_sum]
  simp only [endAct_homothety, endAct_verschiebungInt]
  exact hAdd (sum_mem_of_add X X' γ γ' hAdd Finset.univ _ _ fun k _ =>
      mem_S_homothety X X' γ γ' (K + 1) (e k) (pi_basis_mem X X' γ γ' ha ha' K k))
    (mem_S_V X X' γ γ' (hK.pi hz))

include hK ha ha' hAdd hSmul in
theorem succ_frobγ {j : Zp2 p →+* B} (hγ : X.IsHomogeneousVBasis j γ)
    (hPi : ∀ {x : CartierModule p X.F} {x' : CartierModule p X'.F}, (x, x') ∈ S X X' γ γ' (K + 1) →
      (endAct X.varpiEnd x, endAct X'.varpiEnd x') ∈ S X X' γ γ' (K + 1))
    (i : Fin 2) : (frobenius (γ i), frobenius (γ' i)) ∈ S X X' γ γ' (K + 1) := by
  obtain ⟨η, θ, hpW, hθη⟩ := exists_natCast_eq_teichmuller_add_verschiebung_unit_map p (B := B)
  have hVinj := verschiebungInt_injective_of_algebra_padicInt p X.F
  have hVinj' := verschiebungInt_injective_of_algebra_padicInt p X'.F
  have haa := a_zero_mul X X' γ γ' hγ ha ha' i
  obtain ⟨t, t', ht, h1, h1'⟩ := pi_basis X X' γ γ' ha ha' (K + 1) i
  obtain ⟨t₂, t₂', ht₂, h2, h2'⟩ := pi_basis X X' γ γ' ha ha' (K + 1) (FormalODModule.piIndex 0 i)
  have hz : (homothety (a 0 i ^ p) t₂ + endAct X.varpiEnd t,
      homothety (a 0 i ^ p) t₂' + endAct X'.varpiEnd t') ∈ S X X' γ γ' (K + 1) :=
    hAdd (mem_S_homothety X X' γ γ' (K + 1) _ ht₂) (hPi ht)

  have eqX : verschiebungInt (η • frobenius (γ i)) =
      verschiebungInt (homothety (a 0 i ^ p) t₂ + endAct X.varpiEnd t) := by
    have hp2 := endAct_varpiEnd_varpiEnd X (γ i)
    rw [h1, map_add, endAct_homothety, h2, piIndex_zero_piIndex_zero, endAct_verschiebungInt, map_add,
      ← homothety_mul, homothety_verschiebungInt, haa, ← natCast_smul_eq_nsmul', hpW, add_smul,
      teichmuller_smul, verschiebung_smul_eq, add_assoc, ← map_add] at hp2
    exact (add_left_cancel hp2).symm
  have eqX' : verschiebungInt (η • frobenius (γ' i)) =
      verschiebungInt (homothety (a 0 i ^ p) t₂' + endAct X'.varpiEnd t') := by
    have hp2 := endAct_varpiEnd_varpiEnd X' (γ' i)
    rw [h1', map_add, endAct_homothety, h2', piIndex_zero_piIndex_zero, endAct_verschiebungInt, map_add,
      ← homothety_mul, homothety_verschiebungInt, haa, ← natCast_smul_eq_nsmul', hpW, add_smul,
      teichmuller_smul, verschiebung_smul_eq, add_assoc, ← map_add] at hp2
    exact (add_left_cancel hp2).symm
  have hF : frobenius (γ i) = θ • (homothety (a 0 i ^ p) t₂ + endAct X.varpiEnd t) := by
    rw [← hVinj eqX, smul_smul, hθη, one_smul]
  have hF' : frobenius (γ' i) = θ • (homothety (a 0 i ^ p) t₂' + endAct X'.varpiEnd t') := by
    rw [← hVinj' eqX', smul_smul, hθη, one_smul]
  rw [hF, hF']
  exact hSmul θ hz

include hK hAdd hSmul in
theorem succ_frob
    (hFγ : ∀ i : Fin 2, (frobenius (γ i), frobenius (γ' i)) ∈ S X X' γ γ' (K + 1))
    {x : CartierModule p X.F} {x' : CartierModule p X'.F} (hx : (x, x') ∈ S X X' γ γ' (K + 1 + 1)) :
    (frobenius x, frobenius x') ∈ S X X' γ γ' (K + 1) := by
  obtain ⟨e, z, z', hz, hx1, hx2⟩ := mem_S_uncons X X' γ γ' hx
  rw [hx1, hx2, map_add, map_add, map_sum, map_sum]
  simp only [frobenius_homothety, frobenius_verschiebungInt_eq_smul]
  exact hAdd (sum_mem_of_add X X' γ γ' hAdd Finset.univ _ _ fun k _ =>
    mem_S_homothety X X' γ γ' (K + 1) _ (hFγ k)) (hSmul _ hz)

end Succ

section All

open CerednikDrinfeld

variable [Algebra (PadicInt p) B] {j : Zp2 p →+* B} {a : ℕ → Fin 2 → B}
  (X X' : FormalODModule p B) (γ : Fin 2 → CartierModule p X.F) (γ' : Fin 2 → CartierModule p X'.F)
  (hγ : X.IsHomogeneousVBasis j γ)
  (ha : X.HasStructureConstants γ a) (ha' : X'.HasStructureConstants γ' a)

include hγ ha ha' in
theorem good_succ {K : ℕ} (hK : Good X X' γ γ' K) : Good X X' γ γ' (K + 1) := by
  have hAdd : ∀ {x y : CartierModule p X.F} {x' y' : CartierModule p X'.F},
      (x, x') ∈ S X X' γ γ' (K + 1) → (y, y') ∈ S X X' γ γ' (K + 1) →
        (x + y, x' + y') ∈ S X X' γ γ' (K + 1) := fun {x y x' y'} hx hy => succ_add X X' γ γ' hK hx hy
  have hSmul : ∀ (w : WittVector p B) {x : CartierModule p X.F} {x' : CartierModule p X'.F},
      (x, x') ∈ S X X' γ γ' (K + 1) → (w • x, w • x') ∈ S X X' γ γ' (K + 1) :=
    fun w {x x'} hx => succ_smul X X' γ γ' hK w hx
  have hPi : ∀ {x : CartierModule p X.F} {x' : CartierModule p X'.F}, (x, x') ∈ S X X' γ γ' (K + 1) →
      (endAct X.varpiEnd x, endAct X'.varpiEnd x') ∈ S X X' γ γ' (K + 1) :=
    fun {x x'} hx => succ_pi X X' γ γ' hK ha ha' hAdd hx
  have hFγ : ∀ i : Fin 2, (frobenius (γ i), frobenius (γ' i)) ∈ S X X' γ γ' (K + 1) :=
    succ_frobγ X X' γ γ' hK ha ha' hAdd hSmul hγ hPi
  exact ⟨hAdd, hSmul, hPi, hFγ, fun {x x'} hx => succ_frob X X' γ γ' hK hAdd hSmul hFγ hx⟩

include hγ ha ha' in
theorem good_all (K : ℕ) : Good X X' γ γ' K := by
  induction K with
  | zero => exact good_zero X X' γ γ'
  | succ K ih => exact good_succ X X' γ γ' hγ ha ha' ih

end All

end Transfer

end FFromPi
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_forall_hasStructureConstants_frobenius_eq_sum.FFromPi"

open MvFormalGroup MvFormalGroup.CartierModule FFromPi

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [Algebra (PadicInt p) B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (a : ℕ → Fin 2 → B) :
    ∃ c : ℕ → Fin 2 → Fin 2 → B,
      ∀ (X : CerednikDrinfeld.FormalODModule p B) (γ : Fin 2 → MvFormalGroup.CartierModule p X.F),
        X.IsHomogeneousVBasis j γ → X.HasStructureConstants γ a →
        ∀ (i : Fin 2) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p X.F,
          MvFormalGroup.CartierModule.frobenius (γ i) =
            (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[(m : ℕ)]
              (∑ k : Fin 2, MvFormalGroup.CartierModule.homothety (c m i k) (γ k))) +
            (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[N] h := by
  classical
  by_cases hex : ∃ (X₀ : CerednikDrinfeld.FormalODModule p B) (γ₀ : Fin 2 → CartierModule p X₀.F),
      X₀.IsHomogeneousVBasis j γ₀ ∧ X₀.HasStructureConstants γ₀ a
  · obtain ⟨X₀, γ₀, hγ₀, ha₀⟩ := hex
    have H : ∀ (i : Fin 2) (N : ℕ), ∃ (cN : ℕ → Fin 2 → B) (h : CartierModule p X₀.F),
        frobenius (γ₀ i) = ev γ₀ N cN + (⇑(verschiebungInt (p := p) (Φ := X₀.F)))^[N] h := by
      intro i N
      obtain ⟨cN, h, -, h1, -⟩ := (good_all X₀ X₀ γ₀ γ₀ hγ₀ ha₀ ha₀ N).frobγ i
      simp only at h1
      exact ⟨cN, h, h1⟩
    choose cN hN hcN using H
    refine ⟨fun m i k => cN i (m + 1) m k, ?_⟩
    intro X γ hγ ha i N
    obtain ⟨dd, h₀, h, e₀, e⟩ := (good_all X₀ X γ₀ γ hγ₀ ha₀ ha N).frobγ i
    simp only at e₀ e
    have hd : ∀ m, m < N → dd m = cN i (m + 1) m := by
      intro m hm
      have h1 : dd m = cN i N m :=
        ev_unique γ₀ hγ₀.2 N dd (cN i N) h₀ (hN i N) (e₀.symm.trans (hcN i N)) m hm
      rw [h1]
      exact digit_compat γ₀ hγ₀.2 (cN i) (hN i) (frobenius (γ₀ i)) (hcN i) m N hm
    refine ⟨h, ?_⟩
    dsimp only
    rw [e, ev_congr γ N dd (fun m => cN i (m + 1) m) hd, ev_eq_fin_sum]
  · exact ⟨fun _ _ _ => 0, fun X γ hγ ha => (hex ⟨X, γ, hγ, ha⟩).elim⟩

end S_CerednikDrinfeld_FormalODModule_exists_forall_hasStructureConstants_frobenius_eq_sum
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_forall_hasStructureConstants_frobenius_eq_sum (solution)
