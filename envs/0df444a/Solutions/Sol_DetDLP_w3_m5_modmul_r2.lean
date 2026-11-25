-- Prove2me | solution 1 for DetDLP.w3_m5_modmul_r2
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T21:39:27.331901+00:00
-- url     : https://prove2.me/submissions/58afe2d4-8c19-4798-bc0e-304bc53d4738

import Definitions.Def_DetDLP_W3_ModMul
import Theorems.Thm_DetDLP_modular_and_ec_gadget_parsimony

set_option autoImplicit false
open DetDLP DetDLP.w4_M5GraphBounds DetDLP.w4_M5PortTensor DetDLP.w4_ConvolutionArithmetic

private theorem w3_bus_values {d x y u : ℕ} (hx : x<2^d) (hy : y<2^d) (hu : u<2^(2*d)) :
    bitsToNat (fun i : Fin d => w3_mulBus d x y u ⟨i.val,by omega⟩) = x ∧
    bitsToNat (fun i : Fin d => w3_mulBus d x y u ⟨d+i.val,by omega⟩) = y ∧
    bitsToNat (fun i : Fin (2*d) => w3_mulBus d x y u ⟨2*d+i.val,by omega⟩) = u := by
  have get (k z : ℕ) (hz : z<2^k) : bitsToNat (fun i : Fin k => z.testBit i.val) = z := by
    have he : (fun i : Fin k => z.testBit i.val) = canonicalBits k z := funext fun i => Nat.testBit_eq_decide_div_mod_eq ..
    rw [he]; exact bitsToNat_canonicalBits hz
  constructor
  · simpa [w3_mulBus] using get d x hx
  constructor
  · convert get d y hy using 2; funext i; simp [w3_mulBus,show ¬d+i.val < d by omega, show d+i.val < 2*d by omega]
  · convert get (2*d) u hu using 2; funext i; simp [w3_mulBus,show ¬2*d+i.val < d by omega, show ¬2*d+i.val<2*d by omega]

private theorem w3_product_run {d : ℕ} (hd : 1 ≤ d) (x y : ℕ) (hx : x < 2^d) (hy : y < 2^d) :
    (∃! r, w3_mulPins hd x y r) ∧ ∀ r, w3_mulPins hd x y r → r.1.val = x*y := by
  classical
  have pars := parsimonious hd
  have fits : x*y < 2^(2*d) := by
    rw [show 2*d=d+d by omega,pow_add]; exact Nat.mul_lt_mul_of_lt_of_le hx hy.le (Nat.two_pow_pos _)
  have sound (r : w3_mulRun d hd) (hr : w3_mulPins hd x y r) : r.1.val = x*y := by
    obtain ⟨aa,bb,cc⟩ := w3_bus_values hx hy r.1.isLt
    by_contra he
    exact (pars.2 (w3_mulBus d x y r.1.val)).2 (by simpa only [aa,bb,cc] using Ne.symm he) ⟨r.2,hr⟩
  refine ⟨?_,sound⟩
  obtain ⟨aa,bb,cc⟩ := w3_bus_values hx hy fits
  obtain ⟨a,ha,huniq⟩ := (pars.2 (w3_mulBus d x y (x*y))).1 (by exact (congrArg₂ (· * ·) aa bb).trans cc.symm)
  refine ⟨(⟨x*y,fits⟩,a),ha,?_⟩
  rintro ⟨u,b⟩ hb
  have hu : u = ⟨x*y,fits⟩ := Fin.ext (sound (u,b) hb)
  subst u; exact Prod.ext rfl (huniq b hb)

private theorem w3_low {d u z : ℕ} (hz : z < 2^d) :
    (∀ i : Fin d, u.testBit i.val = z.testBit i.val) ↔ u % 2^d = z := by
  have hcan (z : ℕ) (hz' : z < 2^d) : bitsToNat (fun i : Fin d => z.testBit i.val) = z := by
    have he : (fun i : Fin d => z.testBit i.val) = canonicalBits d z := funext fun i => Nat.testBit_eq_decide_div_mod_eq ..
    rw [he]; exact bitsToNat_canonicalBits hz'
  have hbits (i : Fin d) : (u % 2^d).testBit i.val = u.testBit i.val := by simp [Nat.testBit_mod_two_pow,i.isLt]
  constructor
  · intro h; calc u%2^d = _ := (hcan _ (Nat.mod_lt _ (Nat.two_pow_pos _))).symm
                  _ = _ := (congrArg bitsToNat (funext (fun i => (hbits i).trans (h i)))).trans (hcan z hz)
  · intro h i; rw [← h]; exact (hbits i).symm

theorem solution : w3_modMulInterface := by
  intro d hd q x y z hq hq' hx hy hz
  obtain ⟨hprod,prodSound⟩ := w3_product_run hd x y (hx.trans_le hq') (hy.trans_le hq')
  constructor
  · intro eq; subst q; constructor
    · intro h; obtain ⟨r,hr,uniq⟩ := hprod
      exact ⟨r,⟨hr,(w3_low hz).2 ((congrArg (· % 2^d) (prodSound r hr)).trans h.symm)⟩,fun s hs => uniq s hs.1⟩
    · intro r hr; exact (((w3_low hz).1 hr.2).symm.trans (congrArg (· % 2^d) (prodSound r hr.1)))
  · intro strict
    have divlt : x*y/q < q := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0<q)).2
      exact Nat.mul_lt_mul_of_lt_of_le hx hy.le (by omega)
    let θ : Fin (2^d) := ⟨x*y/q,divlt.trans_le hq'⟩
    obtain ⟨hsecond,secondSound⟩ := w3_product_run hd θ.val q θ.isLt strict
    have allSound (r : Fin (2^d) × w3_mulRun d hd × w3_mulRun d hd) (hr : w3_modTwo hd q x y z r) :
        z = (x*y)%q ∧ r.1 = θ := by
      obtain ⟨h1,h2,he⟩ := hr
      have hs := (w3_product_run hd r.1.val q r.1.isLt strict).2 r.2.2 h2
      have hx' := (modular_and_ec_gadget_parsimony.2.1 q x y z r.1.val r.2.1.1.val r.2.2.1.val hx hy hz).1
        ⟨(prodSound _ h1).symm,hs.symm,he⟩
      exact ⟨hx'.1,Fin.ext hx'.2.1⟩
    constructor
    · intro hz'
      obtain ⟨u1,hu1,unique1⟩ := hprod
      obtain ⟨u2,hu2,unique2⟩ := hsecond
      refine ⟨(θ,u1,u2),⟨hu1,hu2,?_⟩,?_⟩
      · change u2.1.val + z = u1.1.val
        rw [secondSound _ hu2,prodSound _ hu1,hz']; exact Nat.div_add_mod' _ _
      · rintro ⟨t,a,b⟩ hr
        have ht : t = θ := (allSound _ hr).2; subst t
        exact Prod.ext rfl (Prod.ext (unique1 _ hr.1) (unique2 _ hr.2.1))
    · exact fun r hr => (allSound r hr).1
