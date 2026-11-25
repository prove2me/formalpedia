-- Prove2me | solution 1 for DetDLP.w3_native_lookup_address
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T00:26:54.647122+00:00
-- url     : https://prove2.me/submissions/f4fda98e-44e1-4e2b-bec3-86eef709ce1e

import Definitions.Def_DetDLP_W3_Separator

set_option autoImplicit false
open DetDLP

private theorem DetDLP.w3_affine_bucket_inj {p : ℕ} [Fact p.Prime]
    (a : Fin (p-1)) (b : Fin p) {x y : ZMod p}
    (h : ((a.val+1)*x.val + b.val)%p = ((a.val+1)*y.val + b.val)%p) : x = y := by
  have ha : a.val+1 < p := by have := a.isLt; omega
  have hne : ((a.val+1 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt ha, ZMod.val_zero] at hv
    omega
  have he := congrArg (fun n : ℕ => (n : ZMod p)) h
  simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val] at he
  exact mul_left_cancel₀ (by simpa only [Nat.cast_add,Nat.cast_one] using hne) (add_right_cancel he)

private def DetDLP.w3_ec_bucket {p m : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)}
    (T : ℕ) (s : ECSeed p m) (i : Fin m) : E.toAffine.Point → ℕ
  | .zero => 2*T
  | .some x y _ => let b := decide (y.val%2 = 1); let ab := s i b
                   ((ab.1.val+1)*x.val + ab.2.val)%p + (if b then T else 0)

private theorem DetDLP.w3_ec_bucket_spec {p m : ℕ} [hp : Fact p.Prime] (hp2 : 2 < p)
    (E : WeierstrassCurve (ZMod p)) (h1 : E.a₁ = 0) (h3 : E.a₃ = 0)
    (T : ℕ) (s : ECSeed p m) (i : Fin m) :
    Set.InjOn (w3_ec_bucket (E := E) T s i) (ecFactorBlock E T s i) ∧
    ∀ X ∈ ecFactorBlock E T s i, w3_ec_bucket T s i X < 2*T := by
  classical
  have mem {X : E.toAffine.Point} (hx : X ∈ ecFactorBlock E T s i) : ecFactorMem T s i X = true :=
    (Finset.mem_filter.mp hx).2
  constructor
  · intro X hx Y hy he
    have hX := mem hx; have hY := mem hy
    cases X with
    | zero => simp [ecFactorMem] at hX
    | some x y hx' =>
      cases Y with
      | zero => simp [ecFactorMem] at hY
      | some u v hy' =>
        let b := decide (y.val%2 = 1); let c := decide (v.val%2 = 1)
        let f := fun (t : Bool) (z : ZMod p) => (((s i t).1.val+1)*z.val+(s i t).2.val)%p
        change decide (f b x < T) = true at hX
        change decide (f c u < T) = true at hY
        change f b x + (if b then T else 0) = f c u + (if c then T else 0) at he
        have hlt := of_decide_eq_true hX; have hlt' := of_decide_eq_true hY
        have hbc : b = c := by
          cases hb : b <;> cases hc : c <;> simp_all only [Bool.false_eq_true, if_false, if_true] <;> omega
        rw [←hbc] at he
        have hx0 : x = u := w3_affine_bucket_inj _ _ (add_right_cancel he)
        subst u
        have hpar : y.val % 2 = v.val % 2 := by
          change decide (y.val%2 = 1) = decide (v.val%2 = 1) at hbc
          simp only [decide_eq_decide] at hbc
          omega
        have hyv : y = v := by
          rcases E.toAffine.Y_eq_of_X_eq hx'.1 hy'.1 rfl with h|h
          · exact h
          · change y = -v - E.a₁*x - E.a₃ at h
            simp only [h1,h3,zero_mul,sub_zero] at h
            by_cases hv : v = 0
            · simpa [hv] using h
            · letI : NeZero v := ⟨hv⟩
              rw [h, ZMod.val_neg_of_ne_zero] at hpar
              have := hp.out.mod_two_eq_one_iff_ne_two.mpr (by omega : p ≠ 2)
              have := v.val_lt
              omega
        subst v; rfl
  · intro X hx
    have h := mem hx
    cases X with
    | zero => simp [ecFactorMem] at h
    | some x y hz =>
      simp only [ecFactorMem,decide_eq_true_eq] at h
      simp only [w3_ec_bucket]
      split <;> omega

theorem solution (q : w3_Query) (hq : w3_fpQueries q ∨ w3_ecQueries q) :
    ∀ i : Fin q.m, Function.Injective (q.addr i) ∧ ∀ r, q.addr i r < 2^q.k := by
  classical
  rcases hq with hq|hq
  · obtain ⟨p,hp,_,_,_,_,s,F,hF,P,y,pre,rfl⟩ := hq
    let m := blockCount (bitLen p); let T := hashThreshold p (p-1) m (p-1)
    intro i
    let l := (F i).map Additive.ofMul
    have hmem (r : Fin l.length) : ((l.get r).toMul) ∈ fpFactorBlock T s i := by
      rw [←(hF i).2, List.mem_toFinset]
      simpa [l] using List.get_mem l r
    constructor
    · intro r t he
      have hv : (((l.get r).toMul : (ZMod p)ˣ) : ZMod p) = ((l.get t).toMul : (ZMod p)ˣ) :=
        w3_affine_bucket_inj (s i).1 (s i).2 he
      have hu := Units.ext hv
      have hnd : l.Nodup := (hF i).1.map Additive.ofMul.injective
      exact (List.nodup_iff_injective_get.mp hnd) (congrArg Additive.ofMul hu)
    · intro r
      have h := (Finset.mem_filter.mp (hmem r)).2
      simp only [fpFactorMem,decide_eq_true_eq] at h
      exact h.trans_le ((show T ≤ 2*T by omega).trans (Nat.le_pow_clog (by decide : 1 < 2) _))
  · obtain ⟨p,hp,E,_,ha1,_,ha3,hp67,_,_,_,s,F,hF,P,y,pre,rfl⟩ := hq
    letI := ecPointFintype E
    let M := Fintype.card E.toAffine.Point; let m := blockCount (bitLen p); let T := hashThreshold p (M-1) m M
    intro i
    have hmem (r : Fin (F i).length) : (F i).get r ∈ ecFactorBlock E T s i := by
      rw [←(hF i).2, List.mem_toFinset]; exact List.get_mem ..
    obtain ⟨hinj,hlt⟩ := w3_ec_bucket_spec (by omega) E ha1 ha3 T s i
    refine ⟨fun r t he => ((hF i).1.get_inj_iff).mp (hinj (hmem r) (hmem t) he),?_⟩
    exact fun r => (hlt _ (hmem r)).trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)
