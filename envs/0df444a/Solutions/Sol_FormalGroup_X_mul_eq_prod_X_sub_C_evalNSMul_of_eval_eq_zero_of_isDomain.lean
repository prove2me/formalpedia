-- Prove2me | solution 1 for FormalGroup.X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/86f2059b-63f9-586d-a8de-54f8a8965a20

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Theorems.Thm_FormalGroup_evalNSMul_mul_eq_zero_of_eval_eq_zero
import Theorems.Thm_FormalGroup_exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain

set_option autoImplicit false

open IsLocalRing Polynomial MvPowerSeries MvFormalGroup

namespace FullSetDomAsm

variable {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T]

theorem adicEval_rename {σ τ : Type*} [Finite σ] [Finite τ] {w : τ → T} (hw : ∀ t, w t ∈ I.radical)
    (e : σ ↪ τ) (f : MvPowerSeries σ T) :
    adicEval (R := T) I w (rename e f) = adicEval (R := T) I (fun s => w (e s)) f := by
  rw [rename_eq_subst, adicEval_subst (R := T) I hw (HasSubst.X_comp e)]
  congr 1
  funext s
  exact adicEval_X (R := T) I w (e s)

theorem eval_eq_adicEval (F : FormalGroup T) (a b : T) :
    (letI : WithIdeal T := ⟨I⟩; F.eval a b) = adicEval (R := T) I ![a, b] F.toPowerSeries := rfl

theorem evalSeries_eq_adicEval (f : PowerSeries T) (x : T) :
    (letI : WithIdeal T := ⟨I⟩; FormalGroup.evalSeries f x) = adicEval (R := T) I (fun _ : Unit => x) f := rfl

theorem val_nsmul_zero_eq_evalNSMul (F : FormalGroup T) (n : ℕ) (P : Points (ofFormalGroup F) T I) :
    (n • P).val 0 = (letI : WithIdeal T := ⟨I⟩; F.evalNSMul n (P.val 0)) := by
  letI : WithIdeal T := ⟨I⟩
  induction n with
  | zero =>
    rw [zero_nsmul, FormalGroup.evalNSMul_zero]
    rfl
  | succ n ih =>
    rw [succ_nsmul, FormalGroup.evalNSMul_succ, Points.val_add, eval_eq_adicEval I]
    show adicEval (R := T) I (Sum.elim (n • P).val P.val) (rename e2 F.toPowerSeries) = _
    have hw : ∀ t, Sum.elim (n • P).val P.val t ∈ I.radical := by
      rintro (j | j)
      · exact (n • P).mem_radical j
      · exact P.mem_radical j
    rw [adicEval_rename I hw e2]
    congr 1
    funext s
    fin_cases s
    · show Sum.elim (n • P).val P.val (e2 0) = (letI : WithIdeal T := ⟨I⟩; F.evalNSMul n (P.val 0))
      rw [e2_zero, Sum.elim_inl, ih]
    · show Sum.elim (n • P).val P.val (e2 1) = P.val 0
      rw [e2_one, Sum.elim_inr]

end FullSetDomAsm

set_option maxHeartbeats 6400000 in
theorem solution
    (T : Type*) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (F : FormalGroup T) [F.IsComm] (q : ℕ) [Fact q.Prime] (hq0 : (q : T) ≠ 0)
    (g : T[X]) (hmonic : g.Monic) (hdeg : g.natDegree = q - 1)
    (hdist : ∀ i < q - 1, g.coeff i ∈ maximalIdeal T)
    (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v)
    (x : T) (hx : x ∈ maximalIdeal T) (hg : g.eval x = 0) :
    Polynomial.X * g = ∏ a ∈ Finset.range q, (Polynomial.X - Polynomial.C (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul a x)) := by
  classical
  letI : WithIdeal T := ⟨maximalIdeal T⟩
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  let P : Points (ofFormalGroup F) T (maximalIdeal T) := ⟨fun _ => x, fun _ => Ideal.le_radical hx⟩
  have hB := FullSetDomAsm.val_nsmul_zero_eq_evalNSMul (maximalIdeal T) F
  have hrad : (maximalIdeal T).radical = maximalIdeal T := (maximalIdeal.isMaximal T).isPrime.radical
  have hmem : ∀ n : ℕ, (n • P).val 0 ∈ maximalIdeal T := fun n => by
    have := (n • P).mem_radical 0; rwa [hrad] at this

  have hqP : q • P = 0 := by
    apply Points.ext
    funext i
    rw [Subsingleton.elim i 0, Points.val_zero]
    have := FormalGroup.evalNSMul_mul_eq_zero_of_eval_eq_zero T F q g hmonic hdeg hdist v hv hF x hx hg 1
    rw [← hB 1 P, one_nsmul] at this
    rw [hB q P]
    exact this

  have hroot : ∀ n : ℕ, (Polynomial.X * g).eval ((n • P).val 0) = 0 := by
    intro n
    have hqn : q • (n • P) = 0 := by rw [smul_smul, mul_comm, ← smul_smul, hqP, smul_zero]
    have hval : F.evalNSMul q ((n • P).val 0) = 0 := by
      rw [← hB q (n • P), hqn, Points.val_zero]
    have hserQ : ∀ Q : Points (ofFormalGroup F) T (maximalIdeal T),
        FormalGroup.evalSeries (F.nthSeries q) (Q.val 0) = F.evalNSMul q (Q.val 0) := by
      intro Q
      rw [← hB q Q, Points.val_nsmul, nthSeries_ofFormalGroup]
      show _ = adicEval (R := T) (maximalIdeal T) Q.val (toMv (F.nthSeries q))
      rw [toMv_def, FullSetDomAsm.adicEval_rename (maximalIdeal T) Q.mem_radical e1]
      rfl
    have hser := hserQ (n • P)
    obtain ⟨e, he, hep⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal T) ((n • P).val 0) (hmem n)
    have : e (F.nthSeries q) = 0 := by rw [← he, hser, hval]
    rw [hF, ← Polynomial.coe_X, ← Polynomial.coe_mul, map_mul, hep] at this
    exact (IsUnit.mul_left_eq_zero (hv.map e)).mp this

  have hxne : x ≠ 0 := by
    intro hx0
    have hg0 : g.eval 0 = 0 := by rw [hx0] at hg; exact hg
    exact hq0 (((FormalGroup.exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero T F q g hmonic hdeg hdist v hv hF).2).mp hg0)

  have hord_q : addOrderOf P ∣ q := addOrderOf_dvd_of_nsmul_eq_zero hqP
  have key : ∀ a b : ℕ, a < b → b < q → a • P = b • P → False := by
    intro a b hab hb hPab
    have hsplit : (b - a) • P + a • P = b • P := by rw [← add_nsmul, Nat.sub_add_cancel hab.le]
    have hc : (b - a) • P = 0 :=
      add_right_cancel (hsplit.trans (hPab.symm.trans (zero_add _).symm))
    have hcop : Nat.Coprime q (b - a) :=
      Nat.coprime_of_lt_prime (Nat.sub_ne_zero_of_lt hab) (by omega) (Fact.out : q.Prime)
    have hdvd : addOrderOf P ∣ Nat.gcd q (b - a) := Nat.dvd_gcd hord_q (addOrderOf_dvd_of_nsmul_eq_zero hc)
    rw [hcop] at hdvd
    have hP0 : P = 0 := AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    exact hxne (congrArg (fun Q : Points (ofFormalGroup F) T (maximalIdeal T) => Q.val 0) hP0)
  have hinj : ∀ a b : ℕ, a < q → b < q → (a • P).val 0 = (b • P).val 0 → a = b := by
    intro a b ha hb hab
    have hPab : a • P = b • P := Points.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact hab)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key a b h hb hPab
    · exact key b a h ha hPab.symm

  have hmon : (Polynomial.X * g).Monic := Polynomial.monic_X.mul hmonic
  have hne0 : Polynomial.X * g ≠ 0 := hmon.ne_zero
  have hdegq : (Polynomial.X * g).natDegree = q := by
    rw [mul_comm, Polynomial.natDegree_mul_X hmonic.ne_zero, hdeg]; omega
  let y : ℕ → T := fun a => (a • P).val 0
  have hyev : ∀ a, y a = F.evalNSMul a x := fun a => hB a P
  have hinjOn : Set.InjOn y ↑(Finset.range q) := fun a ha b hb h =>
    hinj a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h
  let S : Finset T := (Finset.range q).image y
  have hScard : S.card = q := by rw [Finset.card_image_of_injOn hinjOn, Finset.card_range]
  have hSsub : S.val ≤ (Polynomial.X * g).roots := by
    rw [Multiset.le_iff_subset S.nodup]
    intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hz)
    exact (Polynomial.mem_roots hne0).mpr (hroot a)
  have hcard : (Polynomial.X * g).roots.card = (Polynomial.X * g).natDegree := by
    apply le_antisymm (Polynomial.card_roots' _)
    rw [hdegq, ← hScard]
    exact Multiset.card_le_card hSsub
  have hroots : (Polynomial.X * g).roots = S.val :=
    (Multiset.eq_of_le_of_card_le hSsub (by rw [hcard, hdegq, ← hScard]; rfl)).symm
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard
  rw [← hprod, hroots, ← Finset.prod_eq_multiset_prod, Finset.prod_image hinjOn]
  exact Finset.prod_congr rfl (fun a _ => by rw [hyev])

end S_FormalGroup_X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain
end P2MW
export P2MW.S_FormalGroup_X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain (solution)
