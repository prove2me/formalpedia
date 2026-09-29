-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/754294bc-9d5f-5ffc-a074-7f9b265e232c

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Theorems.Thm_WittVector_exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem
import Theorems.Thm_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree

set_option autoImplicit false

universe u

noncomputable section

namespace B28U3

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

section Alg
variable {p : ℕ} [hp : Fact p.Prime]

@[reducible] def algebraPadicInt {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B) :
    Algebra (PadicInt p) B :=
  (j.comp ((WittVector.map (algebraMap (ZMod p) (GaloisField p 2))).comp
    (WittVector.equiv p).symm.toRingHom)).toAlgebra

end Alg

section Transfer

p2m_open "CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData"

variable {p : ℕ} [hp : Fact p.Prime] {B : Type} [CommRing B] {j : CerednikDrinfeld.Zp2 p →+* B}

section ev

variable (D : GradedCartierModuleData p B j)

def ev (δ : Fin 2 → D.M) (K : ℕ) (c : ℕ → Fin 2 → B) : D.M :=
  ∑ m ∈ Finset.range K, (⇑D.verschiebung)^[m] (∑ k : Fin 2, WittVector.teichmuller p (c m k) • δ k)

def scons (e : Fin 2 → B) (c : ℕ → Fin 2 → B) : ℕ → Fin 2 → B := fun m => Nat.casesOn m e c

omit hp in
@[scoped simp] theorem scons_zero (e : Fin 2 → B) (c : ℕ → Fin 2 → B) : scons e c 0 = e := rfl
omit hp in
@[scoped simp] theorem scons_succ (e : Fin 2 → B) (c : ℕ → Fin 2 → B) (m : ℕ) : scons e c (m + 1) = c m := rfl

theorem iterate_V_add' (N : ℕ) (a b : D.M) :
    (⇑D.verschiebung)^[N] (a + b) = (⇑D.verschiebung)^[N] a + (⇑D.verschiebung)^[N] b := by
  induction N generalizing a b with
  | zero => rfl
  | succ N ih => simp only [Function.iterate_succ_apply', ih, map_add]

theorem iterate_V_zero' (N : ℕ) : (⇑D.verschiebung)^[N] (0 : D.M) = 0 :=
  Function.iterate_fixed (map_zero _) N

theorem ev_zero (δ : Fin 2 → D.M) (c : ℕ → Fin 2 → B) : ev D δ 0 c = 0 := by
  simp [ev]

theorem ev_succ (δ : Fin 2 → D.M) (K : ℕ) (c : ℕ → Fin 2 → B) :
    ev D δ (K + 1) c = (∑ k : Fin 2, WittVector.teichmuller p (c 0 k) • δ k) +
      D.verschiebung (ev D δ K (fun m => c (m + 1))) := by
  rw [ev, Finset.sum_range_succ', ev, map_sum]
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
  rw [add_comm]

theorem ev_scons (δ : Fin 2 → D.M) (K : ℕ) (e : Fin 2 → B) (c : ℕ → Fin 2 → B) :
    ev D δ (K + 1) (scons e c) = (∑ k : Fin 2, WittVector.teichmuller p (e k) • δ k) +
      D.verschiebung (ev D δ K c) := by
  rw [ev_succ]; rfl

theorem ev_const_zero (δ : Fin 2 → D.M) (K : ℕ) : ev D δ K (fun _ _ => 0) = 0 := by
  simp [ev, WittVector.teichmuller_zero]

theorem ev_add (δ : Fin 2 → D.M) (K L : ℕ) (c : ℕ → Fin 2 → B) :
    ∃ r, ev D δ (K + L) c = ev D δ K c + (⇑D.verschiebung)^[K] r := by
  induction K generalizing c with
  | zero => exact ⟨ev D δ (0 + L) c, by simp [ev_zero]⟩
  | succ K ih =>
    obtain ⟨r, hr⟩ := ih (fun m => c (m + 1))
    refine ⟨r, ?_⟩
    rw [Nat.succ_add, ev_succ, ev_succ, hr, map_add, Function.iterate_succ_apply', add_assoc]

end ev

section S

variable (D D' : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (γ' : Fin 2 → D'.M)

def S (K : ℕ) : Set (D.M × D'.M) :=
  {q | ∃ (c : ℕ → Fin 2 → B) (h : D.M) (h' : D'.M),
    q.1 = ev D γ K c + (⇑D.verschiebung)^[K] h ∧ q.2 = ev D' γ' K c + (⇑D'.verschiebung)^[K] h'}

theorem mem_S_zero (q : D.M × D'.M) : q ∈ S D D' γ γ' 0 :=
  ⟨fun _ _ => 0, q.1, q.2, by simp [ev_zero], by simp [ev_zero]⟩

theorem mem_S_iterate (K : ℕ) (h : D.M) (h' : D'.M) :
    ((⇑D.verschiebung)^[K] h, (⇑D'.verschiebung)^[K] h') ∈ S D D' γ γ' K :=
  ⟨fun _ _ => 0, h, h', by rw [ev_const_zero, zero_add], by rw [ev_const_zero, zero_add]⟩

theorem mem_S_cons {K : ℕ} {z : D.M} {z' : D'.M}
    (hz : (z, z') ∈ S D D' γ γ' K) (e : Fin 2 → B) :
    ((∑ k : Fin 2, WittVector.teichmuller p (e k) • γ k) + D.verschiebung z,
      (∑ k : Fin 2, WittVector.teichmuller p (e k) • γ' k) + D'.verschiebung z') ∈ S D D' γ γ' (K + 1) := by
  obtain ⟨c, h, h', h1, h2⟩ := hz
  simp only at h1 h2
  refine ⟨scons e c, h, h', ?_, ?_⟩
  · show _ = _
    rw [h1, map_add, ev_scons, Function.iterate_succ_apply', add_assoc]
  · show _ = _
    rw [h2, map_add, ev_scons, Function.iterate_succ_apply', add_assoc]

theorem mem_S_uncons {K : ℕ} {x : D.M} {x' : D'.M}
    (hx : (x, x') ∈ S D D' γ γ' (K + 1)) :
    ∃ (e : Fin 2 → B) (z : D.M) (z' : D'.M),
      (z, z') ∈ S D D' γ γ' K ∧ x = (∑ k : Fin 2, WittVector.teichmuller p (e k) • γ k) + D.verschiebung z ∧
        x' = (∑ k : Fin 2, WittVector.teichmuller p (e k) • γ' k) + D'.verschiebung z' := by
  obtain ⟨c, h, h', h1, h2⟩ := hx
  simp only at h1 h2
  refine ⟨c 0, ev D γ K (fun m => c (m + 1)) + (⇑D.verschiebung)^[K] h,
    ev D' γ' K (fun m => c (m + 1)) + (⇑D'.verschiebung)^[K] h',
    ⟨fun m => c (m + 1), h, h', rfl, rfl⟩, ?_, ?_⟩
  · rw [h1, ev_succ, map_add, Function.iterate_succ_apply', add_assoc]
  · rw [h2, ev_succ, map_add, Function.iterate_succ_apply', add_assoc]

theorem mem_S_V {K : ℕ} {z : D.M} {z' : D'.M}
    (hz : (z, z') ∈ S D D' γ γ' K) :
    (D.verschiebung z, D'.verschiebung z') ∈ S D D' γ γ' (K + 1) := by
  have h := mem_S_cons D D' γ γ' hz (fun _ => 0)
  simpa [WittVector.teichmuller_zero] using h

theorem zero_mem_S (K : ℕ) : ((0 : D.M), (0 : D'.M)) ∈ S D D' γ γ' K := by
  have h := mem_S_iterate D D' γ γ' K 0 0
  rwa [iterate_V_zero', iterate_V_zero'] at h

theorem sum_mem_of_add {K : ℕ}
    (hadd : ∀ {x y : D.M} {x' y' : D'.M},
      (x, x') ∈ S D D' γ γ' K → (y, y') ∈ S D D' γ γ' K → (x + y, x' + y') ∈ S D D' γ γ' K)
    {ι : Type*} (s : Finset ι) (f : ι → D.M) (f' : ι → D'.M)
    (h : ∀ i ∈ s, (f i, f' i) ∈ S D D' γ γ' K) :
    (∑ i ∈ s, f i, ∑ i ∈ s, f' i) ∈ S D D' γ γ' K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_S D D' γ γ' K
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact hadd (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end S

section Good

variable (D D' : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (γ' : Fin 2 → D'.M)

structure Good (K : ℕ) : Prop where
  add : ∀ {x y : D.M} {x' y' : D'.M},
    (x, x') ∈ S D D' γ γ' K → (y, y') ∈ S D D' γ γ' K → (x + y, x' + y') ∈ S D D' γ γ' K
  smul : ∀ (w : WittVector p B) {x : D.M} {x' : D'.M},
    (x, x') ∈ S D D' γ γ' K → (w • x, w • x') ∈ S D D' γ γ' K
  pi : ∀ {x : D.M} {x' : D'.M},
    (x, x') ∈ S D D' γ γ' K → (D.varpi x, D'.varpi x') ∈ S D D' γ γ' K
  frobγ : ∀ i : Fin 2, (D.frobenius (γ i), D'.frobenius (γ' i)) ∈ S D D' γ γ' K

theorem good_zero : Good D D' γ γ' 0 :=
  ⟨fun _ _ => mem_S_zero D D' γ γ' _, fun _ _ _ _ => mem_S_zero D D' γ γ' _,
    fun _ => mem_S_zero D D' γ γ' _, fun _ => mem_S_zero D D' γ γ' _⟩

omit D' γ γ' in
theorem sum_teichmuller_ite (δ : Fin 2 → D.M) (jj : Fin 2) (b : B) :
    ∑ k : Fin 2, WittVector.teichmuller p (if k = jj then b else 0) • δ k =
      WittVector.teichmuller p b • δ jj := by
  rw [Finset.sum_eq_single jj]
  · rw [if_pos rfl]
  · intro k _ hk
    rw [if_neg hk, WittVector.teichmuller_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ jj) h

omit D' γ γ' in

theorem smul_eq_teichmuller_add (w : WittVector p B) (x : D.M) :
    w • x = WittVector.teichmuller p (w.coeff 0) • x + D.verschiebung (w.shift 1 • D.frobenius x) := by
  conv_lhs => rw [eq_teichmuller_add_verschiebung_shift w]
  rw [add_smul, ← D.verschiebung_smul_frobenius]

variable {a : ℕ → Fin 2 → B}

theorem pi_basis (ha : D.HasStructureConstants γ a) (ha' : D'.HasStructureConstants γ' a)
    (J : ℕ) (i : Fin 2) :
    ∃ (t : D.M) (t' : D'.M), (t, t') ∈ S D D' γ γ' J ∧
      D.varpi (γ i) =
        WittVector.teichmuller p (a 0 i) • γ (piIndex 0 i) + D.verschiebung t ∧
      D'.varpi (γ' i) =
        WittVector.teichmuller p (a 0 i) • γ' (piIndex 0 i) + D'.verschiebung t' := by
  obtain ⟨r, hr⟩ := ha i (J + 1)
  obtain ⟨r', hr'⟩ := ha' i (J + 1)
  set c : ℕ → Fin 2 → B := fun m k => if k = piIndex (m + 1) i then a (m + 1) i else 0 with hc
  refine ⟨ev D γ J c + (⇑D.verschiebung)^[J] r, ev D' γ' J c + (⇑D'.verschiebung)^[J] r',
    ⟨c, r, r', rfl, rfl⟩, ?_, ?_⟩
  · rw [hr, Fin.sum_univ_eq_sum_range (fun m => (⇑D.verschiebung)^[m]
      (WittVector.teichmuller p (a m i) • γ (piIndex m i))) (J + 1), Finset.sum_range_succ']
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply', map_add, ev, map_sum, hc,
      sum_teichmuller_ite]
    abel
  · rw [hr', Fin.sum_univ_eq_sum_range (fun m => (⇑D'.verschiebung)^[m]
      (WittVector.teichmuller p (a m i) • γ' (piIndex m i))) (J + 1), Finset.sum_range_succ']
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply', map_add, ev, map_sum, hc,
      sum_teichmuller_ite]
    abel

theorem pi_basis_mem (ha : D.HasStructureConstants γ a) (ha' : D'.HasStructureConstants γ' a)
    (J : ℕ) (i : Fin 2) :
    (D.varpi (γ i), D'.varpi (γ' i)) ∈ S D D' γ γ' (J + 1) := by
  obtain ⟨t, t', ht, h1, h2⟩ := pi_basis D D' γ γ' ha ha' J i
  have key := mem_S_cons D D' γ γ' ht (fun k => if k = piIndex 0 i then a 0 i else 0)
  rw [sum_teichmuller_ite, sum_teichmuller_ite] at key
  rwa [h1, h2]

omit D D' γ γ' in
theorem piIndex_zero_piIndex_zero (i : Fin 2) : piIndex 0 (piIndex 0 i) = i := by
  ext; simp only [piIndex]; omega

theorem a_zero_mul (hγ : D.IsHomogeneousVBasis γ)
    (ha : D.HasStructureConstants γ a) (ha' : D'.HasStructureConstants γ' a) (i : Fin 2) :
    a 0 i * a 0 (piIndex 0 i) = p := by
  letI : Algebra (PadicInt p) B := algebraPadicInt j
  obtain ⟨η, θ, hpW, -⟩ := exists_natCast_eq_teichmuller_add_verschiebung_unit_map p (B := B)
  obtain ⟨t, t', -, h1, -⟩ := pi_basis D D' γ γ' ha ha' 0 i
  obtain ⟨t₂, t₂', -, h3, -⟩ := pi_basis D D' γ γ' ha ha' 0 (piIndex 0 i)

  have key := D.varpi_varpi (γ i)
  rw [h1, map_add, D.varpi_smul, h3, piIndex_zero_piIndex_zero, D.varpi_verschiebung, smul_add,
    smul_smul, ← map_mul, D.smul_verschiebung, add_assoc, ← map_add] at key

  have hp2 : ((p : ℕ) • γ i : D.M) = WittVector.teichmuller p (p : B) • γ i +
      D.verschiebung (η • D.frobenius (γ i)) := by
    rw [← Nat.cast_smul_eq_nsmul (WittVector p B), hpW, add_smul, ← D.verschiebung_smul_frobenius]

  obtain ⟨cy, -, huniq⟩ := hγ.2 ((p : ℕ) • γ i)
  have e1 : ((fun k => if k = i then a 0 i * a 0 (piIndex 0 i) else 0),
      WittVector.frobenius (WittVector.teichmuller p (a 0 i)) • t₂ + D.varpi t) = cy := by
    apply huniq
    show (p : ℕ) • γ i = _
    rw [sum_teichmuller_ite]
    exact key.symm
  have e2 : ((fun k => if k = i then (p : B) else 0), η • D.frobenius (γ i)) = cy := by
    apply huniq
    show (p : ℕ) • γ i = _
    rw [sum_teichmuller_ite]
    exact hp2
  have := congrArg (fun q : (Fin 2 → B) × D.M => q.1 i) (e1.trans e2.symm)
  simpa using this

end Good

section Succ

variable (D D' : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (γ' : Fin 2 → D'.M)

variable {K : ℕ} (hK : Good D D' γ γ' K)

include hK in
private theorem _root_.B28U3.succ_add {x y : D.M} {x' y' : D'.M}
    (hx : (x, x') ∈ S D D' γ γ' (K + 1)) (hy : (y, y') ∈ S D D' γ γ' (K + 1)) :
    (x + y, x' + y') ∈ S D D' γ γ' (K + 1) := by
  obtain ⟨e, z, z', hz, hx1, hx2⟩ := mem_S_uncons D D' γ γ' hx
  obtain ⟨f, u, u', hu, hy1, hy2⟩ := mem_S_uncons D D' γ γ' hy
  set w : Fin 2 → WittVector p B := fun k => WittVector.teichmuller p (e k) + WittVector.teichmuller p (f k)
    with hw
  have inner : (z + u + ∑ k : Fin 2, (w k).shift 1 • D.frobenius (γ k),
      z' + u' + ∑ k : Fin 2, (w k).shift 1 • D'.frobenius (γ' k)) ∈ S D D' γ γ' K :=
    hK.add (hK.add hz hu) (sum_mem_of_add D D' γ γ' hK.add Finset.univ _ _ fun k _ => hK.smul _ (hK.frobγ k))
  have key := mem_S_cons D D' γ γ' inner (fun k => (w k).coeff 0)
  have hX : ∀ k, WittVector.teichmuller p (e k) • γ k + WittVector.teichmuller p (f k) • γ k =
      WittVector.teichmuller p ((w k).coeff 0) • γ k + D.verschiebung ((w k).shift 1 • D.frobenius (γ k)) := by
    intro k
    rw [← add_smul, smul_eq_teichmuller_add]
  have hX' : ∀ k, WittVector.teichmuller p (e k) • γ' k + WittVector.teichmuller p (f k) • γ' k =
      WittVector.teichmuller p ((w k).coeff 0) • γ' k + D'.verschiebung ((w k).shift 1 • D'.frobenius (γ' k)) := by
    intro k
    rw [← add_smul, smul_eq_teichmuller_add]
  have hC : (∑ k : Fin 2, WittVector.teichmuller p (e k) • γ k) + D.verschiebung z +
      ((∑ k : Fin 2, WittVector.teichmuller p (f k) • γ k) + D.verschiebung u) =
      (∑ k : Fin 2, WittVector.teichmuller p ((w k).coeff 0) • γ k) +
        D.verschiebung (z + u + ∑ k : Fin 2, (w k).shift 1 • D.frobenius (γ k)) := by
    rw [add_add_add_comm, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun k _ => hX k,
      Finset.sum_add_distrib, map_add, map_add, map_sum, ← map_add]
    abel
  have hC' : (∑ k : Fin 2, WittVector.teichmuller p (e k) • γ' k) + D'.verschiebung z' +
      ((∑ k : Fin 2, WittVector.teichmuller p (f k) • γ' k) + D'.verschiebung u') =
      (∑ k : Fin 2, WittVector.teichmuller p ((w k).coeff 0) • γ' k) +
        D'.verschiebung (z' + u' + ∑ k : Fin 2, (w k).shift 1 • D'.frobenius (γ' k)) := by
    rw [add_add_add_comm, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun k _ => hX' k,
      Finset.sum_add_distrib, map_add, map_add, map_sum, ← map_add]
    abel
  rw [hx1, hx2, hy1, hy2, hC, hC']
  exact key

p2m_export "B28U3" "succ_add"
include hK in
theorem succ_smul (w : WittVector p B) {x : D.M} {x' : D'.M}
    (hx : (x, x') ∈ S D D' γ γ' (K + 1)) : (w • x, w • x') ∈ S D D' γ γ' (K + 1) := by
  obtain ⟨e, z, z', hz, hx1, hx2⟩ := mem_S_uncons D D' γ γ' hx
  set ww : Fin 2 → WittVector p B := fun k => w * WittVector.teichmuller p (e k) with hww
  have inner : ((∑ k : Fin 2, (ww k).shift 1 • D.frobenius (γ k)) + WittVector.frobenius w • z,
      (∑ k : Fin 2, (ww k).shift 1 • D'.frobenius (γ' k)) + WittVector.frobenius w • z') ∈ S D D' γ γ' K :=
    hK.add (sum_mem_of_add D D' γ γ' hK.add Finset.univ _ _ fun k _ => hK.smul _ (hK.frobγ k)) (hK.smul _ hz)
  have key := mem_S_cons D D' γ γ' inner (fun k => (ww k).coeff 0)
  have hX : ∀ k, w • (WittVector.teichmuller p (e k) • γ k) =
      WittVector.teichmuller p ((ww k).coeff 0) • γ k + D.verschiebung ((ww k).shift 1 • D.frobenius (γ k)) := by
    intro k
    rw [smul_smul, smul_eq_teichmuller_add]
  have hX' : ∀ k, w • (WittVector.teichmuller p (e k) • γ' k) =
      WittVector.teichmuller p ((ww k).coeff 0) • γ' k + D'.verschiebung ((ww k).shift 1 • D'.frobenius (γ' k)) := by
    intro k
    rw [smul_smul, smul_eq_teichmuller_add]
  have hC : w • ((∑ k : Fin 2, WittVector.teichmuller p (e k) • γ k) + D.verschiebung z) =
      (∑ k : Fin 2, WittVector.teichmuller p ((ww k).coeff 0) • γ k) +
        D.verschiebung ((∑ k : Fin 2, (ww k).shift 1 • D.frobenius (γ k)) + WittVector.frobenius w • z) := by
    rw [smul_add, Finset.smul_sum, D.smul_verschiebung, Finset.sum_congr rfl fun k _ => hX k,
      Finset.sum_add_distrib, map_add, map_sum]
    abel
  have hC' : w • ((∑ k : Fin 2, WittVector.teichmuller p (e k) • γ' k) + D'.verschiebung z') =
      (∑ k : Fin 2, WittVector.teichmuller p ((ww k).coeff 0) • γ' k) +
        D'.verschiebung ((∑ k : Fin 2, (ww k).shift 1 • D'.frobenius (γ' k)) + WittVector.frobenius w • z') := by
    rw [smul_add, Finset.smul_sum, D'.smul_verschiebung, Finset.sum_congr rfl fun k _ => hX' k,
      Finset.sum_add_distrib, map_add, map_sum]
    abel
  rw [hx1, hx2, hC, hC']
  exact key

variable {a : ℕ → Fin 2 → B} (ha : D.HasStructureConstants γ a) (ha' : D'.HasStructureConstants γ' a)
  (hAdd : ∀ {x y : D.M} {x' y' : D'.M},
      (x, x') ∈ S D D' γ γ' (K + 1) → (y, y') ∈ S D D' γ γ' (K + 1) → (x + y, x' + y') ∈ S D D' γ γ' (K + 1))
  (hSmul : ∀ (w : WittVector p B) {x : D.M} {x' : D'.M},
    (x, x') ∈ S D D' γ γ' (K + 1) → (w • x, w • x') ∈ S D D' γ γ' (K + 1))

include hK ha ha' hAdd hSmul in
theorem succ_pi {x : D.M} {x' : D'.M} (hx : (x, x') ∈ S D D' γ γ' (K + 1)) :
    (D.varpi x, D'.varpi x') ∈ S D D' γ γ' (K + 1) := by
  obtain ⟨e, z, z', hz, hx1, hx2⟩ := mem_S_uncons D D' γ γ' hx
  rw [hx1, hx2, map_add, map_add, map_sum, map_sum]
  simp only [D.varpi_smul, D'.varpi_smul, D.varpi_verschiebung, D'.varpi_verschiebung]
  exact hAdd (sum_mem_of_add D D' γ γ' hAdd Finset.univ _ _ fun k _ =>
      hSmul _ (pi_basis_mem D D' γ γ' ha ha' K k))
    (mem_S_V D D' γ γ' (hK.pi hz))

include hK ha ha' hAdd hSmul in
theorem succ_frobγ (hγ : D.IsHomogeneousVBasis γ) (hγ' : D'.IsHomogeneousVBasis γ')
    (hPi : ∀ {x : D.M} {x' : D'.M}, (x, x') ∈ S D D' γ γ' (K + 1) →
      (D.varpi x, D'.varpi x') ∈ S D D' γ γ' (K + 1))
    (i : Fin 2) : (D.frobenius (γ i), D'.frobenius (γ' i)) ∈ S D D' γ γ' (K + 1) := by
  letI : Algebra (PadicInt p) B := algebraPadicInt j
  obtain ⟨η, θ, hpW, hθη⟩ := exists_natCast_eq_teichmuller_add_verschiebung_unit_map p (B := B)
  have hVinj : Function.Injective D.verschiebung := hγ.verschiebung_injective
  have hVinj' : Function.Injective D'.verschiebung := hγ'.verschiebung_injective
  have haa := a_zero_mul D D' γ γ' hγ ha ha' i
  obtain ⟨t, t', ht, h1, h1'⟩ := pi_basis D D' γ γ' ha ha' (K + 1) i
  obtain ⟨t₂, t₂', ht₂, h2, h2'⟩ := pi_basis D D' γ γ' ha ha' (K + 1) (piIndex 0 i)
  set σa : WittVector p B := WittVector.frobenius (WittVector.teichmuller p (a 0 i)) with hσa
  have hz : (σa • t₂ + D.varpi t, σa • t₂' + D'.varpi t') ∈ S D D' γ γ' (K + 1) :=
    hAdd (hSmul σa ht₂) (hPi ht)

  have eqX : D.verschiebung (η • D.frobenius (γ i)) = D.verschiebung (σa • t₂ + D.varpi t) := by
    have hp2 := D.varpi_varpi (γ i)
    rw [h1, map_add, D.varpi_smul, h2, piIndex_zero_piIndex_zero, D.varpi_verschiebung, smul_add,
      smul_smul, ← map_mul, haa, D.smul_verschiebung, ← Nat.cast_smul_eq_nsmul (WittVector p B), hpW, add_smul,
      ← D.verschiebung_smul_frobenius, add_assoc, ← map_add] at hp2
    exact (add_left_cancel hp2).symm
  have eqX' : D'.verschiebung (η • D'.frobenius (γ' i)) = D'.verschiebung (σa • t₂' + D'.varpi t') := by
    have hp2 := D'.varpi_varpi (γ' i)
    rw [h1', map_add, D'.varpi_smul, h2', piIndex_zero_piIndex_zero, D'.varpi_verschiebung, smul_add,
      smul_smul, ← map_mul, haa, D'.smul_verschiebung, ← Nat.cast_smul_eq_nsmul (WittVector p B), hpW, add_smul,
      ← D'.verschiebung_smul_frobenius, add_assoc, ← map_add] at hp2
    exact (add_left_cancel hp2).symm
  have hF : D.frobenius (γ i) = θ • (σa • t₂ + D.varpi t) := by
    rw [← hVinj eqX, smul_smul, hθη, one_smul]
  have hF' : D'.frobenius (γ' i) = θ • (σa • t₂' + D'.varpi t') := by
    rw [← hVinj' eqX', smul_smul, hθη, one_smul]
  rw [hF, hF']
  exact hSmul θ hz

end Succ

section All

variable {a : ℕ → Fin 2 → B}
  (D D' : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (γ' : Fin 2 → D'.M)
  (hγ : D.IsHomogeneousVBasis γ) (hγ' : D'.IsHomogeneousVBasis γ')
  (ha : D.HasStructureConstants γ a) (ha' : D'.HasStructureConstants γ' a)

include hγ hγ' ha ha' in
theorem good_succ {K : ℕ} (hK : Good D D' γ γ' K) : Good D D' γ γ' (K + 1) := by
  have hAdd : ∀ {x y : D.M} {x' y' : D'.M},
      (x, x') ∈ S D D' γ γ' (K + 1) → (y, y') ∈ S D D' γ γ' (K + 1) →
        (x + y, x' + y') ∈ S D D' γ γ' (K + 1) := fun {x y x' y'} hx hy => succ_add D D' γ γ' hK hx hy
  have hSmul : ∀ (w : WittVector p B) {x : D.M} {x' : D'.M},
      (x, x') ∈ S D D' γ γ' (K + 1) → (w • x, w • x') ∈ S D D' γ γ' (K + 1) :=
    fun w {x x'} hx => succ_smul D D' γ γ' hK w hx
  have hPi : ∀ {x : D.M} {x' : D'.M}, (x, x') ∈ S D D' γ γ' (K + 1) →
      (D.varpi x, D'.varpi x') ∈ S D D' γ γ' (K + 1) :=
    fun {x x'} hx => succ_pi D D' γ γ' hK ha ha' hAdd hSmul hx
  have hFγ : ∀ i : Fin 2, (D.frobenius (γ i), D'.frobenius (γ' i)) ∈ S D D' γ γ' (K + 1) :=
    succ_frobγ D D' γ γ' hK ha ha' hAdd hSmul hγ hγ' hPi
  exact ⟨hAdd, hSmul, hPi, hFγ⟩

include hγ hγ' ha ha' in
theorem good_all (K : ℕ) : Good D D' γ γ' K := by
  induction K with
  | zero => exact good_zero D D' γ γ'
  | succ K ih => exact good_succ D D' γ γ' hγ hγ' ha ha' ih

end All

end Transfer

end B28U3
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.B28U3"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.B28U3"

open B28U3 in
theorem B28U3.u3_sameDigits
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (D D' : CerednikDrinfeld.GradedCartierModuleData p B j)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (γ' : Fin 2 → D'.M) (hγ' : D'.IsHomogeneousVBasis γ')
    (a : ℕ → Fin 2 → B) (ha : D.HasStructureConstants γ a) (ha' : D'.HasStructureConstants γ' a) :
    let SameDigits : ℕ → D.M → D'.M → Prop := fun N x x' =>
      ∃ c : ℕ → Fin 2 → B,
        (∃ t : D.M, x = (∑ m ∈ Finset.range N, (⇑D.verschiebung)^[m]
            (∑ i : Fin 2, WittVector.teichmuller p (c m i) • γ i)) + (⇑D.verschiebung)^[N] t) ∧
        (∃ t' : D'.M, x' = (∑ m ∈ Finset.range N, (⇑D'.verschiebung)^[m]
            (∑ i : Fin 2, WittVector.teichmuller p (c m i) • γ' i)) + (⇑D'.verschiebung)^[N] t')
    ∀ N : ℕ,
      (∀ (x y : D.M) (x' y' : D'.M), SameDigits N x x' → SameDigits N y y' → SameDigits N (x + y) (x' + y')) ∧
      (∀ (w : WittVector p B) (x : D.M) (x' : D'.M), SameDigits N x x' → SameDigits N (w • x) (w • x')) ∧
      (∀ (x : D.M) (x' : D'.M), SameDigits N x x' → SameDigits N (D.varpi x) (D'.varpi x')) ∧
      (∀ i : Fin 2, SameDigits N (D.frobenius (γ i)) (D'.frobenius (γ' i))) := by
  intro SameDigits N
  have hG := good_all D D' γ γ' hγ hγ' ha ha' N
  have hiff : ∀ (x : D.M) (x' : D'.M), SameDigits N x x' ↔ (x, x') ∈ S D D' γ γ' N := by
    intro x x'
    constructor
    · rintro ⟨c, ⟨t, ht⟩, ⟨t', ht'⟩⟩
      exact ⟨c, t, t', ht, ht'⟩
    · rintro ⟨c, t, t', ht, ht'⟩
      exact ⟨c, ⟨t, ht⟩, ⟨t', ht'⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y x' y' hx hy
    exact (hiff _ _).mpr (hG.add ((hiff _ _).mp hx) ((hiff _ _).mp hy))
  · intro w x x' hx
    exact (hiff _ _).mpr (hG.smul w ((hiff _ _).mp hx))
  · intro x x' hx
    exact (hiff _ _).mpr (hG.pi ((hiff _ _).mp hx))
  · intro i
    exact (hiff _ _).mpr (hG.frobγ i)

noncomputable section

namespace B29U4

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData WittVector

section Digits

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
  (D : GradedCartierModuleData p B j)

variable {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)

theorem iterate_add (n : ℕ) (x y : D.M) :
    (⇑D.verschiebung)^[n] (x + y) = (⇑D.verschiebung)^[n] x + (⇑D.verschiebung)^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      map_add]

theorem iterate_zero' (n : ℕ) : (⇑D.verschiebung)^[n] (0 : D.M) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

include hγ in
theorem iterate_injective (n : ℕ) : Function.Injective ((⇑D.verschiebung)^[n]) :=
  Function.Injective.iterate hγ.verschiebung_injective n

def expd (x : D.M) : (Fin 2 → B) × D.M := Classical.choose (hγ.2 x).exists

theorem expd_spec (x : D.M) :
    x = (∑ i : Fin 2, teichmuller p ((expd D hγ x).1 i) • γ i) + D.verschiebung (expd D hγ x).2 :=
  Classical.choose_spec (hγ.2 x).exists

theorem expd_unique (x : D.M) (c : Fin 2 → B) (y : D.M)
    (h : x = (∑ i : Fin 2, teichmuller p (c i) • γ i) + D.verschiebung y) : (c, y) = expd D hγ x :=
  (hγ.2 x).unique h (expd_spec D hγ x)

omit hγ in
theorem sum_teichmuller_zero : (∑ i : Fin 2, teichmuller p ((0 : Fin 2 → B) i) • γ i) = 0 := by
  simp [teichmuller_zero]

include hγ in
theorem expd_zero_of_eq (c : Fin 2 → B) (y : D.M)
    (h : (0 : D.M) = (∑ i : Fin 2, teichmuller p (c i) • γ i) + D.verschiebung y) : c = 0 ∧ y = 0 := by
  have h0 : (0 : D.M) = (∑ i : Fin 2, teichmuller p ((0 : Fin 2 → B) i) • γ i) + D.verschiebung 0 := by
    rw [sum_teichmuller_zero, map_zero, add_zero]
  have := (expd_unique D hγ 0 c y h).trans (expd_unique D hγ 0 0 0 h0).symm
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

omit hγ in
theorem sum_two_of_eq_zero (π : Fin 2) (c : Fin 2 → B) (h : c (π + 1) = 0) :
    (∑ i : Fin 2, teichmuller p (c i) • γ i) = teichmuller p (c π) • γ π := by
  fin_cases π
  · have h' : c 1 = 0 := h
    simp [Fin.sum_univ_two, h', teichmuller_zero]
  · have h' : c 0 = 0 := h
    simp [Fin.sum_univ_two, h', teichmuller_zero]

omit D hγ in
theorem add_one_add_one (k : Fin 2) : k + 1 + 1 = k := by
  fin_cases k <;> rfl

omit hγ in
theorem decomp (k : Fin 2) (y : D.M) : ∃ u ∈ D.piece k, ∃ v ∈ D.piece (k + 1), y = u + v := by
  have htop : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hy : y ∈ D.piece 0 ⊔ D.piece 1 := by rw [htop]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hy
  fin_cases k
  · exact ⟨u, hu, v, hv, huv.symm⟩
  · exact ⟨v, hv, u, hu, by rw [← huv, add_comm]⟩

omit hγ in
theorem eq_zero_of_mem_mem (k : Fin 2) (z : D.M) (h1 : z ∈ D.piece k) (h2 : z ∈ D.piece (k + 1)) : z = 0 := by
  have hd := Submodule.disjoint_def.1 D.isCompl_piece.disjoint
  fin_cases k
  · exact hd z h1 h2
  · exact hd z h2 h1

theorem expd_graded (k : Fin 2) (x : D.M) (hx : x ∈ D.piece k) :
    (expd D hγ x).1 (k + 1) = 0 ∧ (expd D hγ x).2 ∈ D.piece (k + 1) := by
  set c := (expd D hγ x).1 with hc
  set y := (expd D hγ x).2 with hy
  have hxe : x = (∑ i : Fin 2, teichmuller p (c i) • γ i) + D.verschiebung y := expd_spec D hγ x
  obtain ⟨u, hu, v, hv, hyuv⟩ := decomp D k y
  set c' : Fin 2 → B := Pi.single (k + 1) (c (k + 1)) with hc'
  have hc'k : c' (k + 1 + 1) = 0 := by
    rw [hc', add_one_add_one, Pi.single_eq_of_ne]
    intro h; fin_cases k <;> exact absurd h (by decide)
  have hsum' : (∑ i : Fin 2, teichmuller p (c' i) • γ i) = teichmuller p (c (k + 1)) • γ (k + 1) := by
    rw [sum_two_of_eq_zero D (k + 1) c' hc'k, hc', Pi.single_eq_same]
  have hsum : (∑ i : Fin 2, teichmuller p (c i) • γ i) =
      teichmuller p (c k) • γ k + teichmuller p (c (k + 1)) • γ (k + 1) := by
    fin_cases k <;> simp [Fin.sum_univ_two, add_comm]
  have hv'1 : teichmuller p (c (k + 1)) • γ (k + 1) + D.verschiebung u ∈ D.piece (k + 1) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 (k + 1))) (D.verschiebung_mem k u hu)
  have hv'0 : teichmuller p (c (k + 1)) • γ (k + 1) + D.verschiebung u ∈ D.piece k := by
    have heq : teichmuller p (c (k + 1)) • γ (k + 1) + D.verschiebung u =
        x - (teichmuller p (c k) • γ k + D.verschiebung v) := by
      rw [hxe, hsum, hyuv, map_add]; abel
    rw [heq]
    refine Submodule.sub_mem _ hx (Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 k)) ?_)
    have := D.verschiebung_mem (k + 1) v hv
    rwa [add_one_add_one] at this
  have hzero : teichmuller p (c (k + 1)) • γ (k + 1) + D.verschiebung u = 0 :=
    eq_zero_of_mem_mem D k _ hv'0 hv'1
  have h0 : (0 : D.M) = (∑ i : Fin 2, teichmuller p (c' i) • γ i) + D.verschiebung u := by
    rw [hsum', hzero]
  obtain ⟨hc'0, hu0⟩ := expd_zero_of_eq D hγ c' u h0
  refine ⟨?_, ?_⟩
  · have := congrFun hc'0 (k + 1)
    rwa [hc', Pi.single_eq_same] at this
  · rw [hyuv, hu0, zero_add]; exact hv

def S (γ : Fin 2 → D.M) (N : ℕ) (c : ℕ → Fin 2 → B) : D.M :=
  ∑ m ∈ Finset.range N, (⇑D.verschiebung)^[m] (∑ i : Fin 2, teichmuller p (c m i) • γ i)

omit hγ in
theorem S_zero (c : ℕ → Fin 2 → B) : S D γ 0 c = 0 := by simp [S]

omit hγ in
theorem S_succ (N : ℕ) (c : ℕ → Fin 2 → B) :
    S D γ (N + 1) c = S D γ N c + (⇑D.verschiebung)^[N] (∑ i : Fin 2, teichmuller p (c N i) • γ i) := by
  rw [S, S, Finset.sum_range_succ]

omit hγ in
theorem S_congr (N : ℕ) (c c' : ℕ → Fin 2 → B) (h : ∀ m, m < N → c m = c' m) :
    S D γ N c = S D γ N c' := by
  unfold S
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [h m (Finset.mem_range.1 hm)]

def rest (x : D.M) : ℕ → D.M
  | 0 => x
  | m + 1 => (expd D hγ (rest x m)).2

def dig (x : D.M) : ℕ → Fin 2 → B := fun m => (expd D hγ (rest D hγ x m)).1

theorem rest_succ (x : D.M) (m : ℕ) :
    rest D hγ x m = (∑ i : Fin 2, teichmuller p (dig D hγ x m i) • γ i) + D.verschiebung (rest D hγ x (m + 1)) :=
  expd_spec D hγ (rest D hγ x m)

theorem dig_spec (x : D.M) (N : ℕ) : x = S D γ N (dig D hγ x) + (⇑D.verschiebung)^[N] (rest D hγ x N) := by
  induction N with
  | zero => simp [S_zero, rest]
  | succ N ih =>
    rw [S_succ, add_assoc, Function.iterate_succ_apply, ← iterate_add]
    conv_lhs => rw [ih, rest_succ D hγ x N]

theorem dig_unique (N : ℕ) : ∀ (x : D.M) (c : ℕ → Fin 2 → B) (t : D.M),
    x = S D γ N c + (⇑D.verschiebung)^[N] t → (∀ m, m < N → c m = dig D hγ x m) ∧ t = rest D hγ x N := by
  induction N with
  | zero =>
    intro x c t h
    refine ⟨fun m hm => absurd hm (Nat.not_lt_zero m), ?_⟩
    simpa [S_zero, rest] using h.symm
  | succ N ih =>
    intro x c t h
    rw [S_succ, add_assoc, Function.iterate_succ_apply, ← iterate_add] at h
    obtain ⟨hlow, hrest⟩ := ih x c _ h
    have hu := expd_unique D hγ (rest D hγ x N) (c N) t hrest.symm
    refine ⟨fun m hm => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
      · exact hlow m hm
      · exact congrArg Prod.fst hu
    · exact congrArg Prod.snd hu

def par (k : Fin 2) : ℕ → Fin 2
  | 0 => k
  | m + 1 => par k m + 1

omit D hγ in
theorem par_succ (k : Fin 2) (m : ℕ) : par k (m + 1) = par k m + 1 := rfl

theorem rest_mem_and_dig_eq_zero (k : Fin 2) (x : D.M) (hx : x ∈ D.piece k) (m : ℕ) :
    rest D hγ x m ∈ D.piece (par k m) ∧ dig D hγ x m (par k m + 1) = 0 := by
  induction m with
  | zero => exact ⟨hx, (expd_graded D hγ _ _ hx).1⟩
  | succ m ih =>
    have h1 : rest D hγ x (m + 1) ∈ D.piece (par k (m + 1)) := (expd_graded D hγ _ _ ih.1).2
    exact ⟨h1, (expd_graded D hγ _ _ h1).1⟩

end Digits
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.B28U3"

section More

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
  (D : GradedCartierModuleData p B j)

theorem map_S (γ : Fin 2 → D.M) (n : ℕ) (c : ℕ → Fin 2 → B) :
    D.verschiebung (S D γ n c) = S D γ (n + 1) (fun m => match m with | 0 => 0 | m + 1 => c m) := by
  unfold S
  rw [Finset.sum_range_succ', map_sum]
  simp only [Function.iterate_zero_apply]
  have h0 : (∑ i : Fin 2, teichmuller p ((0 : Fin 2 → B) i) • γ i) = 0 := by simp [teichmuller_zero]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Function.iterate_succ_apply']

theorem S_single (γ : Fin 2 → D.M) (i : Fin 2) (n : ℕ) :
    S D γ (n + 1) (fun m l => if m = 0 ∧ l = i then 1 else 0) = γ i := by
  unfold S
  rw [Finset.sum_range_succ']
  have hrest : (∑ m ∈ Finset.range n, (⇑D.verschiebung)^[m + 1]
      (∑ l : Fin 2, teichmuller p ((fun m l => if m = 0 ∧ l = i then (1 : B) else 0) (m + 1) l) • γ l)) = 0 := by
    refine Finset.sum_eq_zero fun m _ => ?_
    have : (∑ l : Fin 2, teichmuller p ((fun m l => if m = 0 ∧ l = i then (1 : B) else 0) (m + 1) l) • γ l) = 0 := by
      simp [teichmuller_zero]
    rw [this, iterate_zero']
  rw [hrest, zero_add, Function.iterate_zero_apply]
  fin_cases i <;> simp [Fin.sum_univ_two, teichmuller_zero]

theorem S_digits_zero (γ : Fin 2 → D.M) (N : ℕ) : S D γ N (0 : ℕ → Fin 2 → B) = 0 := by
  unfold S
  refine Finset.sum_eq_zero fun m _ => ?_
  have : (∑ l : Fin 2, teichmuller p ((0 : ℕ → Fin 2 → B) m l) • γ l) = 0 := by simp [teichmuller_zero]
  rw [this, iterate_zero']

end More
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.B28U3"

section Limit

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
  (D' : GradedCartierModuleData p B j) (γ' : Fin 2 → D'.M) (hcpl : D'.IsVAdicallyComplete)

def lim (c : ℕ → Fin 2 → B) : D'.M :=
  Classical.choose (hcpl (fun m => ∑ i : Fin 2, teichmuller p (c m i) • γ' i)).exists

theorem lim_spec (c : ℕ → Fin 2 → B) (N : ℕ) :
    ∃ t, lim D' γ' hcpl c = S D' γ' N c + (⇑D'.verschiebung)^[N] t :=
  Classical.choose_spec (hcpl (fun m => ∑ i : Fin 2, teichmuller p (c m i) • γ' i)).exists N

theorem lim_unique (c : ℕ → Fin 2 → B) (s : D'.M)
    (hs : ∀ N, ∃ t, s = S D' γ' N c + (⇑D'.verschiebung)^[N] t) : s = lim D' γ' hcpl c :=
  (hcpl (fun m => ∑ i : Fin 2, teichmuller p (c m i) • γ' i)).unique hs (lim_spec D' γ' hcpl c)

end Limit
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.B28U3"

section G

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
  (D : GradedCartierModuleData p B j) {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
  (D' : GradedCartierModuleData p B j) (γ' : Fin 2 → D'.M) (hcpl : D'.IsVAdicallyComplete)

def SD (N : ℕ) (x : D.M) (x' : D'.M) : Prop :=
  ∃ c : ℕ → Fin 2 → B,
    (∃ t : D.M, x = S D γ N c + (⇑D.verschiebung)^[N] t) ∧
    (∃ t' : D'.M, x' = S D' γ' N c + (⇑D'.verschiebung)^[N] t')

def g (x : D.M) : D'.M := lim D' γ' hcpl (dig D hγ x)

theorem SD_g (x : D.M) (N : ℕ) : SD D (γ := γ) D' γ' N x (g D hγ D' γ' hcpl x) :=
  ⟨dig D hγ x, ⟨rest D hγ x N, dig_spec D hγ x N⟩, lim_spec D' γ' hcpl _ N⟩

theorem eq_g (x : D.M) (x' : D'.M) (h : ∀ N, SD D (γ := γ) D' γ' N x x') : x' = g D hγ D' γ' hcpl x := by
  refine lim_unique D' γ' hcpl _ x' fun N => ?_
  obtain ⟨c, ⟨t, ht⟩, ⟨t', ht'⟩⟩ := h N
  have hc := (dig_unique D hγ N x c t ht).1
  exact ⟨t', by rw [ht', S_congr D' N c (dig D hγ x) hc]⟩

theorem SD_zero_iff (x : D.M) (x' : D'.M) : SD D (γ := γ) D' γ' 0 x x' := by
  exact ⟨0, ⟨x, by simp [S_zero]⟩, ⟨x', by simp [S_zero]⟩⟩

end G
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.B28U3"

section Main

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

omit p B j in
theorem fin_two_cases (π l : Fin 2) : l = π ∨ l = π + 1 := by
  fin_cases π <;> fin_cases l <;> simp

theorem par_succ_base (k : Fin 2) (m : ℕ) : par (k + 1) m = par k m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [par_succ, par_succ, ih]

theorem sum_add_of_disjoint (D' : GradedCartierModuleData p B j) (γ' : Fin 2 → D'.M) (π : Fin 2)
    (e f : Fin 2 → B) (he : e (π + 1) = 0) (hf : f π = 0) :
    (∑ l : Fin 2, teichmuller p (e l + f l) • γ' l) =
      (∑ l : Fin 2, teichmuller p (e l) • γ' l) + ∑ l : Fin 2, teichmuller p (f l) • γ' l := by
  fin_cases π
  · have he' : e 1 = 0 := he
    have hf' : f 0 = 0 := hf
    simp [Fin.sum_univ_two, he', hf', teichmuller_zero]
  · have he' : e 0 = 0 := he
    have hf' : f 1 = 0 := hf
    simp [Fin.sum_univ_two, he', hf', teichmuller_zero, add_comm]

theorem S_add_of_disjoint (D' : GradedCartierModuleData p B j) (γ' : Fin 2 → D'.M) (k : Fin 2)
    (e f : ℕ → Fin 2 → B) (he : ∀ m, e m (par k m + 1) = 0) (hf : ∀ m, f m (par k m) = 0) (N : ℕ) :
    S D' γ' N (fun m l => e m l + f m l) = S D' γ' N e + S D' γ' N f := by
  unfold S
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← iterate_add, ← sum_add_of_disjoint D' γ' (par k m) (e m) (f m) (he m) (hf m)]

theorem aUnique_of_U3
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (D D' : GradedCartierModuleData p B j)
    (hD : D.IsSpecialCartierModule) (hD' : D'.IsSpecialCartierModule)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (γ' : Fin 2 → D'.M) (hγ' : D'.IsHomogeneousVBasis γ')
    (a : ℕ → Fin 2 → B) (ha : D.HasStructureConstants γ a) (ha' : D'.HasStructureConstants γ' a)
    (hU3 : let SameDigits : ℕ → D.M → D'.M → Prop := fun N x x' =>
      ∃ c : ℕ → Fin 2 → B,
        (∃ t : D.M, x = (∑ m ∈ Finset.range N, (⇑D.verschiebung)^[m]
            (∑ i : Fin 2, WittVector.teichmuller p (c m i) • γ i)) + (⇑D.verschiebung)^[N] t) ∧
        (∃ t' : D'.M, x' = (∑ m ∈ Finset.range N, (⇑D'.verschiebung)^[m]
            (∑ i : Fin 2, WittVector.teichmuller p (c m i) • γ' i)) + (⇑D'.verschiebung)^[N] t')
    ∀ N : ℕ,
      (∀ (x y : D.M) (x' y' : D'.M), SameDigits N x x' → SameDigits N y y' → SameDigits N (x + y) (x' + y')) ∧
      (∀ (w : WittVector p B) (x : D.M) (x' : D'.M), SameDigits N x x' → SameDigits N (w • x) (w • x')) ∧
      (∀ (x : D.M) (x' : D'.M), SameDigits N x x' → SameDigits N (D.varpi x) (D'.varpi x')) ∧
      (∀ i : Fin 2, SameDigits N (D.frobenius (γ i)) (D'.frobenius (γ' i)))) :
    ∃ g : D.M →+ D'.M, (∀ i, g (γ i) = γ' i) ∧
      Function.Bijective g ∧
      (∀ (w : WittVector p B) (x : D.M), g (w • x) = w • g x) ∧
      (∀ x, g (D.frobenius x) = D'.frobenius (g x)) ∧
      (∀ x, g (D.verschiebung x) = D'.verschiebung (g x)) ∧
      (∀ x, g (D.varpi x) = D'.varpi (g x)) ∧
      (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → g x ∈ D'.piece i) := by
  have U : ∀ N : ℕ,
      (∀ (x y : D.M) (x' y' : D'.M), SD D (γ := γ) D' γ' N x x' → SD D (γ := γ) D' γ' N y y' →
        SD D (γ := γ) D' γ' N (x + y) (x' + y')) ∧
      (∀ (w : WittVector p B) (x : D.M) (x' : D'.M), SD D (γ := γ) D' γ' N x x' →
        SD D (γ := γ) D' γ' N (w • x) (w • x')) ∧
      (∀ (x : D.M) (x' : D'.M), SD D (γ := γ) D' γ' N x x' → SD D (γ := γ) D' γ' N (D.varpi x) (D'.varpi x')) ∧
      (∀ i : Fin 2, SD D (γ := γ) D' γ' N (D.frobenius (γ i)) (D'.frobenius (γ' i))) := hU3
  set G : D.M → D'.M := g D hγ D' γ' hD'.2 with hG
  have hSDG : ∀ x N, SD D (γ := γ) D' γ' N x (G x) := SD_g D hγ D' γ' hD'.2
  have heq : ∀ x x', (∀ N, SD D (γ := γ) D' γ' N x x') → x' = G x := eq_g D hγ D' γ' hD'.2

  have hadd : ∀ x y, G (x + y) = G x + G y := fun x y =>
    (heq (x + y) (G x + G y) fun N => (U N).1 _ _ _ _ (hSDG x N) (hSDG y N)).symm
  have hsmul : ∀ (w : WittVector p B) x, G (w • x) = w • G x := fun w x =>
    (heq (w • x) (w • G x) fun N => (U N).2.1 _ _ _ (hSDG x N)).symm
  have hvarpi : ∀ x, G (D.varpi x) = D'.varpi (G x) := fun x =>
    (heq (D.varpi x) (D'.varpi (G x)) fun N => (U N).2.2.1 _ _ (hSDG x N)).symm

  have hV : ∀ x, G (D.verschiebung x) = D'.verschiebung (G x) := by
    intro x
    refine (heq (D.verschiebung x) (D'.verschiebung (G x)) fun N => ?_).symm
    cases N with
    | zero => exact SD_zero_iff D D' γ' _ _
    | succ n =>
      obtain ⟨c, ⟨t, ht⟩, ⟨t', ht'⟩⟩ := hSDG x n
      refine ⟨fun m => match m with | 0 => 0 | m + 1 => c m, ⟨t, ?_⟩, ⟨t', ?_⟩⟩
      · conv_lhs => rw [ht]
        rw [map_add, map_S, Function.iterate_succ_apply']
      · conv_lhs => rw [ht']
        rw [map_add, map_S, Function.iterate_succ_apply']

  have hF : ∀ x, G (D.frobenius x) = D'.frobenius (G x) := by
    intro x
    apply hγ'.verschiebung_injective
    rw [← hV, ← one_smul (WittVector p B) (D.frobenius x), D.verschiebung_smul_frobenius, hsmul,
      ← D'.verschiebung_smul_frobenius, one_smul]

  have hγi : ∀ i, G (γ i) = γ' i := by
    intro i
    refine (heq (γ i) (γ' i) fun N => ?_).symm
    cases N with
    | zero => exact SD_zero_iff D D' γ' _ _
    | succ n =>
      refine ⟨fun m l => if m = 0 ∧ l = i then 1 else 0, ⟨0, ?_⟩, ⟨0, ?_⟩⟩
      · rw [S_single, iterate_zero', add_zero]
      · rw [S_single, iterate_zero', add_zero]

  have hpiece : ∀ (k : Fin 2) (x : D.M), x ∈ D.piece k → G x ∈ D'.piece k := by
    intro k x hx
    obtain ⟨u, hu, v, hv, huv⟩ := decomp D' k (G x)

    have hpu := fun m => (rest_mem_and_dig_eq_zero D' hγ' k u hu m).2
    have hpv : ∀ m, dig D' hγ' v m (par k m) = 0 := by
      intro m
      have := (rest_mem_and_dig_eq_zero D' hγ' (k + 1) v hv m).2
      rwa [par_succ_base, add_one_add_one] at this
    have hpx := fun m => (rest_mem_and_dig_eq_zero D hγ k x hx m).2

    have h1 : ∀ N, ∃ t', G x = S D' γ' N (dig D hγ x) + (⇑D'.verschiebung)^[N] t' :=
      lim_spec D' γ' hD'.2 (dig D hγ x)
    have h2 : ∀ N, G x = S D' γ' N (fun m l => dig D' hγ' u m l + dig D' hγ' v m l) +
        (⇑D'.verschiebung)^[N] (rest D' hγ' u N + rest D' hγ' v N) := by
      intro N
      rw [S_add_of_disjoint D' γ' k _ _ hpu hpv, iterate_add, huv]
      conv_lhs => rw [dig_spec D' hγ' u N, dig_spec D' hγ' v N]
      abel
    have hdig : ∀ m l, dig D hγ x m l = dig D' hγ' u m l + dig D' hγ' v m l := by
      intro m l
      obtain ⟨t', ht'⟩ := h1 (m + 1)
      have e1 := (dig_unique D' hγ' (m + 1) (G x) _ _ ht').1 m (Nat.lt_succ_self m)
      have e2 := (dig_unique D' hγ' (m + 1) (G x) _ _ (h2 (m + 1))).1 m (Nat.lt_succ_self m)
      have := e1.trans e2.symm
      exact congrFun this l
    have hv0 : ∀ m, dig D' hγ' v m = 0 := by
      intro m
      funext l
      rcases fin_two_cases (par k m) l with rfl | rfl
      · exact hpv m
      · have := hdig m (par k m + 1)
        rw [hpx m, hpu m, zero_add] at this
        exact this.symm
    have hvz : v = 0 := by
      have e1 : v = lim D' γ' hD'.2 0 := by
        refine lim_unique D' γ' hD'.2 0 v fun N => ⟨rest D' hγ' v N, ?_⟩
        rw [← S_congr D' N (dig D' hγ' v) 0 (fun m _ => hv0 m)]
        exact dig_spec D' hγ' v N
      have e2 : (0 : D'.M) = lim D' γ' hD'.2 0 := by
        refine lim_unique D' γ' hD'.2 0 0 fun N => ⟨0, ?_⟩
        rw [S_digits_zero, iterate_zero', add_zero]
      rw [e1, ← e2]
    rw [huv, hvz, add_zero]
    exact hu

  set G' : D'.M → D.M := g D' hγ' D γ hD.2 with hG'
  have hswap : ∀ N x x', SD D (γ := γ) D' γ' N x x' → SD D' (γ := γ') D γ N x' x :=
    fun N x x' ⟨c, h1, h2⟩ => ⟨c, h2, h1⟩
  have hleft : ∀ x, G' (G x) = x := fun x =>
    (eq_g D' hγ' D γ hD.2 (G x) x fun N => hswap N x (G x) (hSDG x N)).symm
  have hright : ∀ x', G (G' x') = x' := fun x' =>
    (heq (G' x') x' fun N => ?_).symm
  swap
  · obtain ⟨c, h1, h2⟩ := SD_g D' hγ' D γ hD.2 x' N
    exact ⟨c, h2, h1⟩
  refine ⟨AddMonoidHom.mk' G hadd, hγi, ?_, hsmul, hF, hV, hvarpi, hpiece⟩
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

end Main
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.B28U3"

end B29U4
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.B28U3"

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (D D' : CerednikDrinfeld.GradedCartierModuleData p B j)
    (hD : D.IsSpecialCartierModule) (hD' : D'.IsSpecialCartierModule)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (γ' : Fin 2 → D'.M) (hγ' : D'.IsHomogeneousVBasis γ')
    (a : ℕ → Fin 2 → B) (ha : D.HasStructureConstants γ a) (ha' : D'.HasStructureConstants γ' a) :
    ∃ g : D.M →+ D'.M, (∀ i, g (γ i) = γ' i) ∧
      Function.Bijective g ∧
      (∀ (w : WittVector p B) (x : D.M), g (w • x) = w • g x) ∧
      (∀ x, g (D.frobenius x) = D'.frobenius (g x)) ∧
      (∀ x, g (D.verschiebung x) = D'.verschiebung (g x)) ∧
      (∀ x, g (D.varpi x) = D'.varpi (g x)) ∧
      (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → g x ∈ D'.piece i) :=
  B29U4.aUnique_of_U3 hB D D' hD hD' γ hγ γ' hγ' a ha ha'
    (B28U3.u3_sameDigits p j hB D D' γ hγ γ' hγ' a ha ha')

end
end S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree (solution)
